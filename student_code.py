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

        # Asserted facts and rules do not have support - retract
        # Asserted facts and rules that have support -> unassert it
        # Inferred facts abd rules that do not have support -> shouldn't exist, retract
        # Inferred facts abd rules that have support -> Do nothing

        # every fact/rule retracted fact/rule supports
            # adjust supported by list
            # if it's no longer supported remove

        print("Retract Fact/Rule: ", fact_rule)

        if isinstance(fact_rule, Fact):
            fact_rule = self._get_fact(fact_rule)

            # asserted facts that do not have support, simply retract.
            if fact_rule.asserted and (len(fact_rule.supported_by) == 0):
                self.facts.remove(fact_rule)

            # asserted facts that have support, unassert.
            elif fact_rule.asserted and (len(fact_rule.supported_by) > 0):
                fact_rule.asserted = False
                return

            # Inferred facts that do not have support, shouldn't exist, retract.
            elif not fact_rule.asserted and (len(fact_rule.supported_by) == 0):
                self.facts.remove(fact_rule)

            # Inferred facts that have support, do nothing, return.
            else:
                return

        elif isinstance(fact_rule, Rule):
            fact_rule = self._get_rule(fact_rule)

            # asserted rules that do not have support, simply retract.
            if fact_rule.asserted and (len(fact_rule.supported_by) == 0):
                self.rules.remove(fact_rule)

            # asserted rules that have support, unassert.
            elif fact_rule.asserted and (len(fact_rule.supported_by) > 0):
                fact_rule.asserted = False
                return

            # Inferred rules that do not have support, shouldn't exist, retract.
            elif not fact_rule.asserted and (len(fact_rule.supported_by) == 0):
                self.rules.remove(fact_rule)

            # Inferred rules that have support, do nothing, return.
            else:
                return


        for fact in fact_rule.supports_facts:
            for fr in fact.supported_by:
                if fr[0] == fact_rule:
                    fact.supported_by.remove(fr)
            if len(fact.supported_by) == 0 and not fact.asserted:
                self.kb_retract(fact)

        for rule in fact_rule.supports_rules:
            for fr in rule.supported_by:
                if (fr[1] == fact_rule):
                    rule.supported_by.remove(fr)
            if len(rule.supported_by) == 0 and not rule.asserted:
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

        # If rule, match only first element of lhs with fact
        # If fact, examine each rule and check the first element of its LHS against new fact.

        # Use the util.match function to do unification and create possible bindings
        # Use the util.instantiate function to bind a variable in the rest of a rule
        # Rules and Facts have fields for supported_by, supports_facts, and supports_rules.
            # For example, imagine that a fact F and rule R matched to infer a new fact/rule fr.
            # fr is supported by F and R. Add them to fr's supported_by list - you can do this by passing them as a constructor argument when creating fr.
            # F and R now support fr. Add fr to the supports_rules and supports_facts lists (as appropriate) in F and R.


        #input
        print("in fc_infer")
        print("input fact: ", fact)
        print("input rule: ", rule)

        # match for possible bindings
        bindings = match(fact.statement, rule.lhs[0])
        print("bindings: ", bindings)

        # If no bindings, return.
        if not bindings:
            return None

        else:
            item = instantiate(rule.rhs, bindings)
            print("item: ", item)

            #TODO removeeeeeeeeeeeeeeee
            index_f = kb.facts.index(fact)
            index_r = kb.rules.index(rule)
            print("index_f")
            print(index_f)
            print("index_r")
            print(index_r)


            # If only one lhs, we can infer a fact
            if len(rule.lhs) == 1:
                print('infer fact not in KB using item')
                infer_fact = Fact(item, [[rule, fact]])

                # add the inferred fact to the KB
                kb.kb_assert(infer_fact)

                # add the inferred fact to the rule's supported fact
                rule.supports_facts.append(infer_fact)

                # add the inferred fact to the fact's supported fact
                fact.supports_facts.append(infer_fact)

                print('added fact to the kb: ', infer_fact)

            # More than one lhs, we can infer rule
            else:
                print('infer rule not in KB using item')
                infer_rules = []
                for r in rule.lhs[1:]:
                    # instantiate the remaining LHS with the binding
                    infer_rules.append(instantiate(r, bindings))

                print('infer rules list', infer_rules)
                # create new rule
                infer_rule = Rule([infer_rules, item], [[rule, fact]])

                # add the inferred rule to the KB
                kb.kb_assert(infer_rule)

                # add the inferred rule to the rule's supported rules
                rule.supports_rules.append(infer_rule)

                # add the inferred fact to the fact's supported rules
                fact.supports_rules.append(infer_rule)

                print('added fact to the kb: ', infer_rule)

