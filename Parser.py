#!/usr/bin/env python2.6
# -*- coding: utf-8 -*-
#
# Parsningsalgoritmer VT12
# Uppgift 2: Shift-reduce
# Daniel Gradin Bergström

import copy  # Used for doing deep copies of Config objects.
import codecs  # For coping with Pythons 2.x's encoding hell.
import sys  # Used for reading input from the terminal.


class Config:

    """ A snapshot of a specific buffer and stack configuration. Also keeps track of the parse tree leading up to that
        configuration using a list containing string representations of the nodes. """

    def __init__(self, inputList):
        self.buffer = inputList
        self.stack = []
        self.tree = []  # List containing the tree structure leading up to this configuration.
        #self.index = 0  # Index number.


class Transit:

    """ Describes a transition of a certain type (i.e. shift or reduce) and between what states the transition applies.
        The toState is always a string (a symbol, a word or a clause element) and the fromState is a string if it's
        a shift transformation or a tuple of strings if it's a reduction (i.e. which constituents that are to be
        reduced)."""

    def __init__(self, transType, toState, fromState):
        self.type = transType
        self.toState = toState
        self.fromState = fromState


class Token:

    """ Describes a token which is a representation of an indexed string (words or symbols in the grammar).
        It is the format in which these words and symbols are stored on the stack and in the buffer. """

    counter = 0

    def __init__(self, token):
        self.symbol = token
        self.index = Token.counter
        Token.counter += 1


class CFG:

    """ A representation of a context free grammar. Contains a lexicon for terminals and a rule dictionary for
        non-terminals. The dictionaries describes valid transformations within the grammar. """

    # The CFG root symbol.
    startSymbol = "S"

    def __init__(self, filename):

        # Dictionaries, one for the terminals (lexicon) and the other for non-terminal rules.
        self.lexicon = {}
        self.rules = {}

        # Load the grammar from file.
        with codecs.open(filename, 'r', 'utf-8') as f:

            for line in f:

                # Strip leading and trailing whitespace (includes newline characters).
                line = line.strip()

                # Split the string into separate tokens.
                elements = line.split()

                # For terminal rules.
                # The format in the dictionary: 'saw': ['vtr', 'n'], 'her': ['NPobj', 'poss']
                if (len(elements) > 2) and elements[1] == "=>":

                    # Try to retrieve an entry from the lexicon using the terminal (i.e. the word) as key, if there is no
                    # matching entry in the lexicon then return an empty list.
                    value = self.lexicon.get(elements[2], [])

                    # Append the LHS symbol of the rule to the list.
                    value.append(elements[0])

                    # Add or update/overwrite the entry to/in the lexicon.
                    self.lexicon[elements[2]] = value

                # For non-terminal rules.
                # The format in the dictionary: ('NP','VP') : ['S', 'VP']
                # It's indexed by tuples (containing at least two constituents) representing the RHS symbols of the rule.
                elif (len(elements) > 2) and elements[1] == "-->":

                    # Try to retrieve the entry for this key (i.e. tuple of symbols) from the dictionary, if there
                    # is no entry in the dictionary matching the key then return an empty list.
                    value = self.rules.get(tuple(elements[2:]), [])

                    # Append the LHS symbol of the rule to the list.
                    value.append(elements[0])

                    # Add or update/overwrite the entry to/in the dictionary.
                    self.rules[tuple(elements[2:])] = value

                # Ignore other kind of lines.
                else:
                    pass


class DepGrammar:

    """ A representation of a dependency grammar. Consists of a dictionary describing valid dependencies between words
        within the grammar. """

    def __init__(self, filename):

        # A dictionary containing the rules within the grammar.
        self.rules = {}

        # Load the grammar from file.
        with codecs.open(filename, 'r', 'utf-8') as f:

            for line in f:

                # Strip leading and trailing whitespace (includes newline characters).
                line = line.strip()

                # Split the string into separate tokens (splitting on ':').
                elements = line.split(":")

                # Adding the dependency descriptions to the dictionary (used by the reduce operation).
                # An example of the format in the dictionary: ('Jag', 'var') : [('LA', 'subj')]
                if (len(elements) == 4) and (elements[2] == "LA" or elements[2] == "RA"):

                    # Try to retrieve an entry matching this key (i.e. tuple of the two words that have a dependancy
                    # between them) from the dictionary, if there is no match in the dictionary then return an empty list.
                    value = self.rules.get(tuple(elements[0:2]), [])

                    # Append a tuple containing the direction of the arc and the clause element to the list.
                    # For example: ('LA', 'subj')
                    value.append(tuple(elements[2:4]))

                    # Add or update/overwrite the entry to/in the dictionary.
                    self.rules[tuple(elements[0:2])] = value

                # Ignore other lines.
                else:
                    pass


class ShiftReduceCFG:

    """ A shift reduce implementation for context free grammars. """

    def __init__(self, filename, inputString):

        # Create a new CFG from file and save a reference.
        self.grammar = CFG(filename)

        # Save a reference to the input string.
        self.inputString = inputString

        # List to hold the representation of the input string as Token objects.
        self.inputList = []

        # Split the input string and add the words as Token objects to the input list.
        for token in inputString.split():
            self.inputList.append(Token(token))

    # Returns a new Config object with the initial input string (as a list of Token objects) loaded in the buffer.
    def initialconfig(self):
        return Config(self.inputList)

    # Checks if a specific configuration (Config object) is a valid parse. For a CFG that means that the root
    # symbol of the specified grammar needs to be the only remaining constituent on the stack (first it checks
    # for a stack depth of 1) and also that the buffer must be empty.
    def accepting(self, config):

        return ((len(config.stack) == 1) and
                (config.stack[-1].symbol == self.grammar.startSymbol) and
                (len(config.buffer) == 0))

    # Find possible transitions from the current state/configuration.
    def findTransits(self, config):

        # List for holding the transitions.
        transits = []

        # If there are terminals in the buffer try to find an appropiate rule within the lexicon for a shift operation.
        if len(config.buffer) > 0:

            # Try to retrieve a list of possible shift transformations for the current terminal from the lexicon,
            # if there are no entry a None reference is returned.
            trans = self.grammar.lexicon.get(config.buffer[0].symbol)

            # Iterate through the possible transitions (if there are any) and create a new Transit object for
            # each of them and add them to the transit list.
            # Type = shift, toState = LHS of the rule (a non-terminal), fromState = RHS of the rule (a terminal/word)
            if trans is not None:
                for tran in trans:
                    transits.append(Transit("shift", toState=tran, fromState=config.buffer[0].symbol))

        # If there are non-terminals on the stack try to find possible transitions for a reduce operation.
        if len(config.stack) > 0:

            # Traverse the stack from the right, increment the left position of the range with one step at
            # every iteration (i.e. it's counting down from the length of the stack subtracted by one (1)).
            for i in xrange(len(config.stack) - 1, -1, -1):

                # Collects the symbols within the current range through list comprehension then converts it to a tuple
                # (used for doing a dictionary lookup). The range is i (current left most position) to the length of
                # the stack.
                key = tuple(config.stack[y].symbol for y in xrange(i, len(config.stack)))

                # Check if there is an entry in the dictionary matching a key consiting of the foremonetioned tuple.
                # If there is then its value is returned, otherwise a None reference is returned.
                trans = self.grammar.rules.get(key)

                # Iterate through the possible transitions (if there are any) and create a new Transit object for
                # each of them and add them to the transit list.
                # Type = reduce, toState = LHS of the rule (a non-terminal), fromState = RHS of the rule (the collection
                # of non-terminals that are to be reduced, represented by a tuple)
                if trans is not None:
                    for tran in trans:
                        transits.append(Transit("reduce", toState=tran, fromState=key))

        # Return the list of possbile transitions.
        return transits

    # Computes a specific transition for a specific configuration.
    def computeTransit(self, config, transit):

        # Makes a deep copy of the current Config-object. No references will be shared.
        # This is to avoid affecting other Config-objects indirectly while also keeping
        # the original Config-object pristine.
        newConfig = copy.deepcopy(config)

        # Create a new token based on the toState of the transition.
        newToken = Token(transit.toState)

        # If the transition is a shift operation.
        if transit.type == "shift":

            # Pop and save the old token from the buffer (used for building the tree representation).
            # Pops at the beginning of the buffer, index 0.
            oldToken = newConfig.buffer.pop(0)

            # Append to the tree.
            newConfig.tree.append(unicode.format(u"{0}:{1}-{2}:{3}", newToken.index, newToken.symbol, oldToken.index, oldToken.symbol))

            # Add the token to the stack.
            newConfig.stack.append(newToken)

        # If the transition is a reduce operation.
        elif transit.type == "reduce":

            # Pop the stack for each constituent involved in the reduce operation,
            # for example ('NP', 'VP') involves popping the stack two times.
            for x in xrange(len(transit.fromState)):

                # Pop and save the old token (used for building the tree representation).
                oldToken = newConfig.stack.pop()

                # Append to the tree.
                newConfig.tree.append(unicode.format(u"{0}:{1}-{2}:{3}", newToken.index, newToken.symbol, oldToken.index, oldToken.symbol))

            # Add the new (reduced) Token object to the stack.
            newConfig.stack.append(newToken)

        # Otherwise do something?
        else:
            return None

        # Return the new configuration.
        return newConfig


class ShiftReduceDEP:

    """ A shift reduce implementation for dependency grammar. """

    def __init__(self, filename, inputString):

        # Create a new DepGrammar from file and save a reference.
        self.grammar = DepGrammar(filename)

        # Save a reference to the input string.
        self.inputString = inputString

        # List to hold the representation of the input string as Token objects.
        self.inputList = []

        # Split the input string and add the words as Token objects to the input list.
        for token in inputString.split():
            self.inputList.append(Token(token))

    # Returns a new Config object with the initial input string (as a list of Token objects) loaded in the buffer.
    def initialconfig(self):
        return Config(self.inputList)

    # Checks if a specific configuration (Config object) is a valid parse. For a dependency grammar that means a
    # stack depth of one (1) (the root) and at the same time an empty buffer.
    def accepting(self, config):

        return ((len(config.stack) == 1) and
                (len(config.buffer) == 0))

    # Find possible transitions from the current state/configuration.
    def findTransits(self, config):

        # List for holding the transitions.
        transits = []

        # If there are terminals in the buffer.
        if len(config.buffer) > 0:

            # Append a transition that pushes the actual word on to the stack.
            transits.append(Transit("shift", toState=config.buffer[0].symbol, fromState=""))

        # For non-terminals on the stack. Two words on the stack is necessary for a reduce operation.
        if len(config.stack) > 1:

            # Make a tuple of the two words that are topmost (rightmost) on the stack.
            key = (config.stack[-2].symbol, config.stack[-1].symbol)

            # Look for transitions within the dictionary.
            transitions = self.grammar.rules.get(key)

            # Iterate through the possible transitions (if there are any) and create a new Transit object for
            # each of them and add them to the transit list.
            # Type = 'RA' or 'LA', toState = the clause element, fromState = the two words (represented by a tuple).
            if transitions is not None:
                for transition in transitions:
                    transits.append(Transit(transition[0], toState=transition[1], fromState=key))

        # Return the list of possbile transitions.
        return transits

    # Computes a specific transition for a specific configuration.
    def computeTransit(self, config, transit):

        # Makes a deep copy of the current Config-object. No references will be shared.
        # This is to avoid affecting other Config-objects indirectly while also keeping
        # the original Config-object pristine.
        newConfig = copy.deepcopy(config)

        # A shift transition.
        if transit.type == "shift":

            # Pop a token from the beginning of the buffer (index 0) and put it on the stack.
            newConfig.stack.append(newConfig.buffer.pop(0))

        # A left arc reduction.
        elif transit.type == "LA":

            # Append the transition to the tree.
            newConfig.tree.append(unicode.format(u"LA: {0}-{1}-{2}",  transit.fromState[1], transit.toState, transit.fromState[0]))

            # Pop the second uppermost token on the stack (the dependent in a LA dependency).
            newConfig.stack.pop(-2)

        # A right arc reduction.
        elif transit.type == "RA":

            # Append the transition to the tree.
            newConfig.tree.append(unicode.format(u"RA: {0}-{1}-{2}",  transit.fromState[0], transit.toState, transit.fromState[1]))

            # Pop the top token of the stack (the dependent in a RA dependency).
            newConfig.stack.pop()

        # Otherwise do something?
        else:
            pass

        # Return the new configuration.
        return newConfig


def parseConfig(system, config):

    """ Parse a specific config considering the specified system. Used recursively for exploring all possible
        transitions from a certain configuration. """

    # Check if the current configuration contains a valid parse (i.e. the ShiftReduce object's accepting method
    # returns true for the current configuration).
    if system.accepting(config) is True:

        # Print the tree structure. The system.inputString must be printed as a string representation of the tuple
        # within the print function call. If not it will give all kinds of encoding/decoding/unicode/ascii errors
        # no matter what I do. I can't seem to fix this which is _extremely_ annoying, especially since printing the
        # tree structure works well (same method does NOT work on the input string somehow ...)!
        print("Valid parse for the string: ", system.inputString)
        for transition in [unicode(i) for i in reversed(config.tree)]:
            print(transition.encode("utf-8"))

        print("")

    # Otherwise continue to find and compute transitions.
    else:

        # Find and save the transitions that are possible considering the current configuration and system.
        transits = system.findTransits(config)

        # Traverse the list of transitions and recursively explore all of them.
        for transit in transits:
            parseConfig(system, system.computeTransit(config, transit))


# Entry point of the program, for testing.
if __name__ == '__main__':

    # CFG parsing.
    system = ShiftReduceCFG("anbn.txt", "a a b b")
    #system = ShiftReduceCFG("isawherduck.txt", "I saw her duck")

    # Retrieve an initial Config object.
    config = system.initialconfig()

    # Begin parsing.
    parseConfig(system, config)

    ##############################

    # DG parsing.
    system = ShiftReduceDEP("depgram.txt", u"Jag var på mötet igår")

    # Retrieve an initial Config object.
    config = system.initialconfig()

    # Begin parsing.
    parseConfig(system, config)

    # Old, remove...
    #system = ShiftReduceCFG(sys.argv[1], sys.argv[2])
    #print(system.grammar.lexicon)
    #print(system.grammar.rules)
    #print(system.grammar.startSymbol)
