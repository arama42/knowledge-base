import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact or Rule) - Fact or Rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_rule):
        """Retract a fact or a rule from the KB

        Args:
            fact_rule (Fact or Rule) - Fact or Rule to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_rule])
        ####################################################
        # Student code goes here

        print("retract  : ", fact_rule)
        kb_item = None

        # Find which type of knowledge base item is the input - rule/fact
        if isinstance(fact_rule, Fact):
            fact_rule = self._get_fact(fact_rule)
            kb_item = self.facts
        elif isinstance(fact_rule, Rule):
            fact_rule = self._get_rule(fact_rule)
            kb_item = self.rules
        else:
            print('Not a valid KB item type')
            return

        # asserted facts/rules that do not have support, simply retract.
        if fact_rule.asserted and not fact_rule.supported_by:
            kb_item.remove(fact_rule)

        # asserted facts/rules that have support, unassert.
        elif fact_rule.asserted and fact_rule.supported_by:
            fact_rule.asserted = False
            return

        # Inferred facts/rules that do not have support shouldn't exist, retract.
        elif not fact_rule.asserted and not fact_rule.supported_by:
            kb_item.remove(fact_rule)

        # Inferred facts/rules that have support, do nothing, return.
        else:
            print('Item is an inferred fact/rule. No action')
            return

        # every fact the retracted fact/rule supports, adjust supported by list.
        # If it's no longer supported, remove.
        for fact in fact_rule.supports_facts:
            for fr in fact.supported_by:
                if fact_rule in fr:
                    fact.supported_by.remove(fr)
            if not fact.supported_by and not fact.asserted:
                self.kb_retract(fact)

        # every rule the retracted fact/rule supports, adjust supported by list.
        # If it's no longer supported, remove.
        for rule in fact_rule.supports_rules:
            for fr in rule.supported_by:
                if fact_rule in fr:
                    rule.supported_by.remove(fr)
            if not rule.supported_by and not rule.asserted:
                self.kb_retract(rule)


class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here

        # analyze inputs
        print("fc_infer")
        print("input fact: ", fact)
        print("input rule: ", rule)

        # If there are no lhs or rhs to the rule, return
        if not rule.lhs or not rule.rhs:
            return None

        # match to do unification and create possible bindings
        bindings = match(fact.statement, rule.lhs[0])
        print("bindings: ", bindings)

        # If no bindings available, return.
        if not bindings:
            return None

        else:
            # Bind variables in the rest of the rule
            bound_item = instantiate(rule.rhs, bindings)
            print("Bound item: ", bound_item)

            no_of_facts = len(kb.facts)
            no_of_rules = len(kb.rules)
            print("Number of facts: ", no_of_facts)
            print("Number of rules: ", no_of_rules)

            # If there is only one lhs in the rule, we can infer a fact
            if len(rule.lhs) == 1:
                print('Infer a fact from bindings and rhs of the rule')
                infer_fact = Fact(bound_item, [[rule, fact]])

                # add the inferred fact to the KB, asserted false
                kb.kb_assert(infer_fact)

                # add the inferred fact to the rule's supported facts list
                rule.supports_facts.append(infer_fact)

                # add the inferred fact to the fact's supported facts list
                fact.supports_facts.append(infer_fact)

                print('Added fact to the kb: ', infer_fact)

            # If rule has more than one lhs, we might infer more rules/ simplify rules in KB.
            else:
                print('Infer rules from in bindings and rhs of the rule')
                infer_rules = []
                for r in rule.lhs[1:]:
                    # Bind variables with the remaining LHS of the rule
                    bound_r = instantiate(r, bindings)
                    infer_rules.append(bound_r)

                print('infer rules list', infer_rules)
                # Infer new rule from binding variables
                infer_rule = Rule([infer_rules, bound_item], [[rule, fact]])

                # add the inferred rule to the KB, asserted false
                kb.kb_assert(infer_rule)

                # add the inferred rule to the rule's supported rules
                rule.supports_rules.append(infer_rule)

                # add the inferred fact to the fact's supported rules
                fact.supports_rules.append(infer_rule)

                print('Added rule to the kb: ', infer_rule)

