import collections
import copy
import sys

dict_of_substituted_value = collections.OrderedDict()
theta = collections.OrderedDict()
fo = open('output.txt', 'w')
askFlag = False
falsify = ''
forLoopDetection = set()
standard_list = []
standard_counter = 1
poo = True


def extractArguments(curr_goal):
    extracted_arg = []
    index1 = curr_goal.index("(")
    index2 = curr_goal.index(")")
    arguments = curr_goal[index1 + 1:index2]
    argList = arguments.split(", ")
    for arg in argList:
        extracted_arg.append(arg.strip())
    return extracted_arg


def extractPredicate(items):
    position = items.index("(")
    return items[0:position].strip()


def standardise_rule(rule):
    global standard_list
    global standard_counter
    dict_of_sub_value = {}
    rule_list = rule.split(" => ")
    lhs = rule_list[0]
    rhs = rule_list[1]
    final_rule = ''
    antecedent_list = lhs.split(" && ")
    replaced_antecedent = ''
    for each_antecedent in antecedent_list:
        each_antecedent_arg_list = extractArguments(each_antecedent)
        arg = []
        for i in range(len(each_antecedent_arg_list)):
            if each_antecedent_arg_list[i][0].islower():
                if each_antecedent_arg_list[i] in standard_list:
                    if dict_of_sub_value.has_key(each_antecedent_arg_list[i]):
                        each_antecedent_arg_list[i] = dict_of_sub_value[each_antecedent_arg_list[i]]
                        arg.append(each_antecedent_arg_list[i])
                    else:
                        dict_of_sub_value[each_antecedent_arg_list[i]] = each_antecedent_arg_list[i] + str(
                                standard_counter)
                        each_antecedent_arg_list[i] = each_antecedent_arg_list[i] + str(standard_counter)
                        standard_counter += 1
                        arg.append(each_antecedent_arg_list[i])

                else:
                    standard_list.append(each_antecedent_arg_list[i])
                    dict_of_sub_value[each_antecedent_arg_list[i]] = each_antecedent_arg_list[i]
                    arg.append(each_antecedent_arg_list[i])
            else:
                arg.append(each_antecedent_arg_list[i])
        replaced_antecedent = replaced_antecedent + arguments_to_complete_goal(each_antecedent, arg) + " && "

    replaced_antecedent = replaced_antecedent[0:replaced_antecedent.rfind("&&")]

    consequent_arguments = extractArguments(rhs)
    arg = []
    for i in range(len(consequent_arguments)):
        if consequent_arguments[i][0].islower():
            if consequent_arguments[i] in standard_list:
                if dict_of_sub_value.has_key(consequent_arguments[i]):
                    consequent_arguments[i] = dict_of_sub_value[consequent_arguments[i]]
                    arg.append(consequent_arguments[i])
                else:
                    dict_of_sub_value[consequent_arguments[i]] = consequent_arguments[i] + str(standard_counter)
                    consequent_arguments[i] = consequent_arguments[i] + str(standard_counter)
                    standard_counter += 1
                    arg.append(consequent_arguments[i])

            else:
                standard_list.append(consequent_arguments[i])
                dict_of_sub_value[consequent_arguments[i]] = consequent_arguments
                arg.append(consequent_arguments[i])
        else:
            arg.append(consequent_arguments[i])
    replaced_consequent = arguments_to_complete_goal(rhs, arg)

    final_rule = replaced_antecedent.strip() + " => " + replaced_consequent.strip()
    return final_rule


def arguments_to_complete_goal(curr_goal, curr_goal_arg_list):
    args = ''
    for item in curr_goal_arg_list:
        args = args + item + ", "
    args = args[0:args.rfind(",")]
    curr_goal = extractPredicate(curr_goal) + '(' + args + ')'
    return curr_goal


def replace_rule(dict_of_sub_value, rule):
    consequent_arguments = extractArguments(rule)

    arg = []
    for each_argument in consequent_arguments:
        if dict_of_sub_value.has_key(each_argument):
            arg.append(dict_of_sub_value.get(each_argument))
        else:
            arg.append(each_argument)
    replaced_rule = arguments_to_complete_goal(rule, arg)

    return replaced_rule.strip()


def check_is_variable(item):
    if item[0][0].islower():
        return True
    else:
        return False


def check_length(item):
    if len(item) == 1:
        return True
    else:
        return False


def unify(x, y, dict_of_substituted_value1):
    dict_of_substituted_value = copy.deepcopy(dict_of_substituted_value1)

    if dict_of_substituted_value is None:
        return None
    elif x == y:
        return dict_of_substituted_value
    elif check_length(x) and check_is_variable(x) and type(x) == list:
        return unify_Var(x, y, dict_of_substituted_value)
    elif check_length(y) and check_is_variable(y) and type(y) == list:
        return unify_Var(y, x, dict_of_substituted_value)
    elif len(x) > 1 and len(y) > 1:
        return unify(x[1:], y[1:], unify([x[0]], [y[0]], dict_of_substituted_value))
    else:
        return None


def unify_Var(var, x, dict_of_substituted_value):
    if var[0] in dict_of_substituted_value:
        return unify([dict_of_substituted_value[var[0]]], x, dict_of_substituted_value)
    elif x[0] in dict_of_substituted_value:
        return unify(var, [dict_of_substituted_value[x[0]]], dict_of_substituted_value)
    else:
        dict_of_substituted_value[var[0]] = x[0]
        return dict_of_substituted_value


def LogPrinting(curr_goal):
    curr_goal_arg_list = extractArguments(curr_goal)
    args = ''
    for item in curr_goal_arg_list:
        if item[0].islower():
            args += "_"  # replace variables by _
        else:
            args = args + item
        args += ", "
    args = args[0:args.rfind(",")]
    curr_goal_log = extractPredicate(curr_goal) + '(' + args + ')'
    return curr_goal_log
    # fo.write('Ask: ' + curr_goal_log + '\n')


def AND(KB, goals, theta):
    global poo
    poo = True
    if theta is None:
        pass
    elif len(goals) == 0:
        yield theta
    else:
        first, rest = goals[0], goals[1:]
        for theta1 in OR(KB, replace_rule(theta, first), theta):  # try printing false here
            for theta2 in AND(KB, rest, theta1):
                yield theta2


def OR(KB, goal, theta):
    global askFlag
    goal_predicate = extractPredicate(goal)
    global poo
    global falsify
    rules = KB.get(goal_predicate)
    counter = 0
    forLoopDetection.add(goal)
    pqr = LogPrinting(goal)
    fo.write("Ask: " + pqr + '\n')
    askFlag = False
    ryr = False
    # print rules,'****rules***'
    for rule in rules:

        # print rule,'============='
        counter += 1
        flag = True

        if rule.find(" => ") > 0:
            std_sentence = standardise_rule(rule)
            rhs = std_sentence.split(" => ")[1]
            lhs = std_sentence.split(" => ")[0].split(" && ")
        else:
            rhs = rule.split(" => ")[0]
            lhs = []

        another_theta = unify(extractArguments(rhs), extractArguments(goal), {})

        if another_theta is None:
            flag = False

        if askFlag:
            if flag:
                # print rule,'============='
                plo = LogPrinting(goal)
                fo.write("Ask: " + plo + '\n')
                askFlag = True

        if flag:
            for theta1 in AND(KB, lhs, unify(extractArguments(rhs), extractArguments(goal), theta)):
                fo.write("True: " + replace_rule(theta1, goal) + '\n')
                ryr = True
                yield theta1
            if counter == len(rules) and ryr == False:
                fo.write("False: " + LogPrinting(replace_rule(theta, goal)) + '\n')
    if not askFlag:
        fo.write("False: " + LogPrinting(replace_rule(theta, goal)) + '\n')
        falsify = goal
        askFlag = True


def ASK(KB, each_query):
    return OR(KB, each_query, {})


def main():
    #fh = open('input.txt', 'r')
    fh = open(sys.argv[2], 'r')
    query = fh.readline()
    query = query.strip()
    ans = False
    KB = collections.OrderedDict()
    global forLoopDetection
    rules = int(fh.readline())
    for i in range(rules):
        # while rules > 0:
        sentence = fh.readline().strip()
        temp_list = []
        sentence = sentence.strip()
        if sentence.find(" => ") > 0:

            # std_sentence = standardise_rule(sentence)

            temp = sentence.split(" => ")

            predicate = extractPredicate(temp[1])

            if KB.has_key(predicate):

                temp_list = KB.get(predicate)
                temp_list.append(sentence.strip())
                KB[predicate] = temp_list

            else:

                temp_list.append(sentence.strip())
                KB[predicate] = temp_list

        else:
            predicate = extractPredicate(sentence)

            if KB.has_key(predicate):

                temp_list = KB.get(predicate)
                temp_list.append(sentence.strip())
                KB[predicate] = temp_list
            else:

                temp_list.append(sentence)
                KB[predicate] = temp_list
                # rules -= 1

    counter = 0
    queries = query.split(" && ")
    i = 0

    for each_query in queries:
        another_flag = False
        forLoopDetection.add(each_query)
        for i in ASK(KB, each_query):
            if i is not None:
                counter += 1
                another_flag = True
            break
        if another_flag and counter == len(queries):
            fo.write('True')
            fo.close()
            quit()
        elif not another_flag:
            # if falsify != each_query:
            #    pooo = LogPrinting(each_query)
            #    fo.write('False: ' + pooo + '\n')
            fo.write("False")
            fo.close()
            quit()


if __name__ == "__main__":
    main()
