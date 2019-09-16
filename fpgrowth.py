from collections import defaultdict


class FPNode:

    def __init__(self, parent, item):
        self.count = 1
        self.parent = parent
        self.item = item
        self.children = {}


class FPTree:

    def join_dicts(d1, d2):
        return {k: d1.get(k, 0) + d2.get(k, 0) for k in set(d1.keys()).union(set(d2.keys()))}

    def __init__(self, db, support, conditional=[]):
        """
        db: Iterable of iterables containing transactions [[transactions], [transactions],...]
        support: Min support. If support < 1 it will be treated as a proportion, else as counts.
        """
        self.support = support
        self.T = len(db)
        self.header = defaultdict(list)
        self.root = FPNode(None, "root")
        self.conditional = conditional
        self.item_counts = {}
        self.db = self._preprocess(db)

        # Insert the transactions into the tree
        for transaction in self.db:
            self._insert_transaction(self.root, transaction, 0)

    def _eval_support(self, item_count):
        """
        Handles the support evaluation
        """
        if self.support < 1:
            return item_count / self.T >= self.support  # Support as proportion
        return item_count >= self.support              # Support as counts

    def _preprocess(self, db):
        """
        Preprocessed the db leaving the 1-itemsets with support >= self.support
        and sorting each transaction in decreasing order of support
        """
        db = [set(row)
              for row in db]  # Ensure each item occurs at most once in each transaction
        counts = dict()
        for row in db:  # Count the appearances of each item in the db
            for item in row:
                if counts.get(item, None) == None:
                    counts[item] = 0
                counts[item] += 1
        to_remove = set()
        for item, count in counts.items():  # Collect items with not enough support
            if not self._eval_support(count):
                to_remove.add(item)
            else:
                self.item_counts[item] = count
        new_db = []
        for row in db:  # Remove low support items from each transaction in db
            new_row = row.difference(to_remove)
            if new_row:
                new_db.append(
                    list(sorted(new_row, key=lambda x: counts[x], reverse=True)))
        return new_db

    def _insert_transaction(self, node, transaction, index):
        """
        Inserts a transaction starting from node 'node' recursively
        """
        if index >= len(transaction):
            return  # Entire transaction has been processed
        # Exists a node for the item at position 'index'
        if transaction[index] in node.children:
            node.children[transaction[index]].count += 1  # Increment the count
        else:
            # Create a new child node for the corresponding item
            node.children[transaction[index]] = FPNode(
                node, transaction[index])
            self.header[transaction[index]].append(
                node.children[transaction[index]])  # Add new node to the header list
        # Recursively add the rest of the transaction
        self._insert_transaction(
            node.children[transaction[index]], transaction, index + 1)

    def combinations(self, transaction):
        """
        Generates all the combinations possible in the transaction
        that meet the support criteria
        """
        ans = {}  # Resulting transactions
        # Iterate over al the binary representations of size len(transaction)
        for i in range(1, 2**len(transaction)):
            comb = []
            index = 0
            comb_support = self.T + 1  # Set the upperbound of the combination support
            while i:  # Check all bits turned on
                if i % 2:  # If bit turned on
                    # Add corresponding transaction to the combination
                    comb.append(transaction[index])
                    # Update support of the combination
                    comb_support = min(
                        comb_support, self.item_counts[transaction[index]])
                index += 1
                i //= 2
            # Add combination if support is high enough
            if self._eval_support(comb_support):
                ans[tuple(comb + self.conditional)] = comb_support
        return ans

    def cond_base(self, cond_item):
        """
        Generates a transactions database from the conditional base of 'cond_item'
        """
        new_db = []
        for node in self.header[cond_item]:  # Iterate over the header list
            # Support of the transaction is the support of 'cond_item'
            support = node.count
            transaction = []
            node = node.parent
            while node.parent:              # Traverse upwards the tree adding the items of the branch to transaction
                transaction.append(node.item)
                node = node.parent
            # Add to the db the transaction 'support' amount of times
            new_db += [transaction[::] for _ in range(support)]
        return new_db

    def is_single_path(self, node):
        """
        Recursively determines whether the tree is a single path or not 
        """
        if len(node.children) == 0:  # If the node has no children then we've finished
            return True
        # If any of the nodes has more than one child then there is not a single path
        elif len(node.children) > 1:
            return False
        # Recursive call with the only child
        return self.is_single_path(next(iter(node.children.values())))

    def generate_patterns(self):
        # Singe path so we need all combinations of that path
        if self.is_single_path(self.root):
            transaction = []
            node = self.root
            while node.children:  # Traverse upwards and save the only transaction
                transaction.append(next(iter(node.children.values())).item)
                node = next(iter(node.children.values()))
            # Make the combinations of the transaction
            return self.combinations(transaction)
        else:  # Not single path tree
            patterns = {}
            for item in self.header:  # For each item in the header
                # Generate the conditional base for 'item' and suffix
                cond_base = self.cond_base(item)
                # Add the patterns generated of 'item' and 'suffix'
                patterns = FPTree.join_dicts(
                    patterns, {tuple([item] + self.conditional): self.item_counts[item]})
                patterns = FPTree.join_dicts(patterns, FPTree(cond_base, self.support, [
                                             item] + self.conditional).generate_patterns())  # Add patterns generated for the conditional tree
            return patterns


class FPGrowth:

    def __init__(self):
        self.db = None
        self.support = None
        self.confidence = None
        self.tree = None
        self.patterns = None

    def fit(self, db, support=1):
        self.db = db
        self.support = support
        self.tree = FPTree(db, support)
        self.patterns = self.tree.generate_patterns()

    def generate(self, confidence=0):
        if self.patterns == None:
            raise Exception("Patterns not calculated")
        rules = []
        sets = {itemset: set(itemset) for itemset in self.patterns}
        for antecedent in self.patterns:
            for consequent in self.patterns:
                if not sets[antecedent].issubset(sets[consequent]):
                    continue
                if antecedent == consequent:
                    continue
                current_confidence = self.patterns[consequent] / \
                    self.patterns[antecedent]
                antecedent_support = self.patterns[antecedent] / self.tree.T
                # If confidence is high enough and lift > 1
                if current_confidence >= confidence and current_confidence / antecedent_support > 1:
                    rules.append({"antecedent": antecedent, "consequent": consequent,
                                  "confidence": current_confidence, "lift": current_confidence / antecedent_support})
        return rules


if __name__ == "__main__":
    # Testing dbs
    db = "125;24;23;124;13;23;13;1235;123"
    db = "adf;acde;bd;bcd;bc;abd;bde;bceg;cdf;abd"
    db = [list(i) for i in db.split(";")]
    fpg = FPGrowth()
    fpg.fit(db, 2)
    patterns = fpg.generate()
    print(patterns)
