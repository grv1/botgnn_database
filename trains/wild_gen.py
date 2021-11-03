#!/usr/bin/python

import sys
import hcb_utils

# sys.path.append('/scratch/postgres/PyGreSQL-3.6.2/')
# import psycopg as pg
import psycopg2 


class Predicate:
    def __init__(self, pred, n, d, a, minv, maxv, md):
        self.name = pred
        self.arity = n
        self.depth = d
        self.args = a
        self.min_var = minv
        self.max_var = maxv
        self.mode = md

    def output(self):
        print('%s(%s)' % (self.name, self.print_args()))

    def print_args(self):
     #       print self.args
        out = 'var_%d' % self.args[0]
        for arg in self.args[1:]:
            out += ',var_%d' % arg

        return out

    def print_untyped_args(self):
        out = '%d' % self.args[0]
        for arg in self.args[1:]:
            out += ',%d' % arg
        return out

    def to_string(self):
        return '%s(%s)' % (self.name, self.print_untyped_args())

    def get_aleph_input(self):
        result = []
        for arg_index in range(len(self.mode.args)):
            if self.mode.args[arg_index] == 'input':
                result.append('[%d]/any' % (arg_index+1))

        if result == []:
            return '[]'

        result_str = '[%s' % result[0]
        for st in result[1:]:
            result_str += ',' + st
        result_str += ']'
        return result_str

    def get_aleph_output(self):
        result = []
        for arg_index in range(len(self.mode.args)):
            if self.mode.args[arg_index] == 'output':
                result.append('[%d]/any' % (arg_index+1))

        if result == []:
            return '[]'

        result_str = '[%s' % result[0]
        for st in result[1:]:
            result_str += ',' + st
        result_str += ']'
        return result_str

    def get_input_args(self):
        result = []
        for arg_index in range(len(self.mode.args)):
            if self.mode.args[arg_index] == 'input':
                result.append(self.args[arg_index])
        return result

    def get_output_args(self):
        result = []
        for arg_index in range(len(self.mode.args)):
            if self.mode.args[arg_index] == 'output':
                result.append(self.args[arg_index])
        return result


class Hypothesis:
    def __init__(self, clause, table, d, minv, maxv, mode_id):
        self.h = clause
        self.t = table
        self.depth = d
        self.min_depth_var = minv
        self.max_depth_var = maxv
        self.mode_index = mode_id

    def output(self):
        self.h[0].output()
        # print ' :- ',
        if len(self.h) > 1:
            for pred in self.h[1:-1]:
                pred.output()
                # print ', ',

            self.h[-1].output()
        # print '.'

    def valid_mode(self, mode):
        if mode.mult == -1:
            return True

        cur_mult = mode.mult
        for pred in self.h:
            if (pred.depth == self.depth and mode is pred.mode):
                if cur_mult == 1:
                    return False
                else:
                    cur_mult -= 1

        return True

    def get_first_extension(self, mode):
        args = [self.min_depth_var for i in range(mode.arity)]
        print(args)
        return Predicate(mode.pred, mode.arity, self.depth, args, -1, -1, mode)

    def get_next_extension(self, mode, last_extension):
        last_args = hcb_utils.copy(last_extension.args)
        print('get_next_extension: last_args: ', last_args)
        cur_max = max(last_args)
        cur_index = len(last_args) - 1
        new_depth = self.depth
        while cur_index >= 0:
            if last_args[cur_index] > self.max_depth_var:
                # overflow, but we know is input argument #
                if last_args[cur_index] < cur_max:
                    last_args[cur_index] += 1
                    new_depth += 1
                    new_min = self.max_depth_var + 1
                    new_max = max([cur_max, last_args[cur_index]])
                    break
                else:
                    last_args[cur_index] = self.min_depth_var
                    cur_index -= 1
                    continue
            elif last_args[cur_index] == self.max_depth_var:
                # overflow, check if output variable #
                if mode.args[cur_index] == 'output':
                    last_args[cur_index] += 1
                    new_depth += 1
                    new_min = self.max_depth_var + 1
                    new_max = max([cur_max, last_args[cur_index]])
                    break
                else:
                    last_args[cur_index] = self.min_depth_var
                    cur_index -= 1
                    continue
            else:
                # no overflow #
                last_args[cur_index] += 1
                new_min = -1
                new_max = -1
                break

        if cur_index < 0:
            return None
        else:
           #         print last_args
            return Predicate(mode.pred, mode.arity, new_depth, last_args, new_min, new_max, mode)


class Mode:
    def __init__(self, m, name, n, a):
        self.pred = name
        self.arity = n
        self.args = a
        self.mult = m


class BottomClause:
    def __init__(self):
        self.hyp_count = 0

    def insert(self, hypothesis, ant_index):
        self.hyp_count += 1
        return self.hyp_count


class BC_Printer(BottomClause):
    def insert(self, hypothesis, ant_index):
        self.hyp_count += 1
        # print 'Hyp number %d:' % self.hyp_count ,
        hypothesis.output()
        return self.hyp_count


class BC_Builder(BottomClause):
    def __init__(self):
        self.hyp_count = 0
        self.lits = [('junk', [])]
        self.last_var = 1

    def insert(self, hypothesis, ant_index):
        self.hyp_count += 1
        cur_lit = hypothesis.h[-1]
        self.lits.append((cur_lit, []))
        self.lits[ant_index][1].append(self.hyp_count)
        tmp_max = max(cur_lit.args)
        if tmp_max > self.last_var:
            self.last_var = tmp_max
        return self.hyp_count

    def print_out(self):
        for i in range(1, len(self.lits)):
            cur_children = self.lits[i][1]
            print('lit ' + str(i) + ' [')
            if cur_children != []:
                print(str(cur_children[0]))

            for desc in cur_children[1:]:
                print(',' + str(desc))

            print('] ')
            self.lits[i][0].output()
            print()

    def output_aleph_bc(self, filename):
        outfile = open(filename, 'w')
        outfile.write(':- eraseall(lits).\n')
        outfile.write(':- eraseall(ivars).\n')
        outfile.write(':- eraseall(ovars).\n')

        outfile.write(':- recorda(lits, lit_info(-1,0,junk,[],[],[]),_).\n')
        outfile.write(':- recorda(ivars, ivars(-1,[]),_).\n')
        outfile.write(':- recorda(ovars, ovars(-1,[]),_).\n')
        for i in range(1, self.hyp_count):
            cur_lit = self.lits[i][0]
            children = self.lits[i][1]
            print_tuple = (i, cur_lit.to_string(), cur_lit.get_aleph_input(
            ), cur_lit.get_aleph_output(), children)
            outfile.write(
                ':- recordz(lits, lit_info(%d,0,%s,%s,%s,%s),_).\n' % print_tuple)
            outfile.write(':- recordz(ivars, ivars(%d,%s),_).\n' %
                          (i, cur_lit.get_input_args()))
            outfile.write(':- recordz(ovars, ovars(%d,%s),_).\n' %
                          (i, cur_lit.get_output_args()))

        outfile.write(':- wild_reset_db_entry(sat,bot_size,%d).\n' %
                      self.hyp_count)
        outfile.write(':- wild_reset_db_entry(sat,last_lit,%d).\n' %
                      self.hyp_count)
        outfile.write(':- wild_reset_db_entry(sat,last_var,%d).\n' %
                      self.last_var)
        outfile.write(':- wild_reset_db_entry(sat,head_ivars,%s).\n' %
                      self.lits[1][0].get_output_args())
        outfile.write(':- wild_reset_db_entry(sat,head_ovars,%s).\n' %
                      self.lits[1][0].get_input_args())

        outfile.close()


def unroll(db, hypothesis, new_table, predicate, mode_id, cur_table_index,db_conn):
    print('Entered unroll with predicate')
    predicate.output()
    new_min = predicate.min_var
    new_max = predicate.max_var
    new_depth = predicate.depth

    cur_hyp = Hypothesis(hypothesis, new_table, new_depth,
                         new_min, new_max, mode_id)
    result = [cur_hyp]

    cur_args = hcb_utils.copy(predicate.args)

    # find output columns #
    output_cols = []
    for i in range(predicate.arity):
        if predicate.mode.args[i] == 'output':
            output_cols.append(i)

    num_output_cols = len(output_cols)
    cur_table = 2

    select_clause = ['tab1.*']
    from_clause = [new_table + ' as tab1']
    where_clause_ids = []
    where_clause_ineqs = []

    while True:
        
        cur_table_name = 'hyp_table_%d' % cur_table_index[0]
        for col in output_cols:
            var_name = predicate.args[col]
            new_max = cur_args[col] + num_output_cols
            cur_args[col] = new_max
            tmpstr = 'tab' + str(cur_table) + '.var_' + \
                str(var_name) + ' as var_' + str(new_max)
            select_clause.append(tmpstr)
            for i in range(1, cur_table):
                tmpstr = 'tab'+str(i)+'.var_' + str(var_name) + \
                    ' <> tab' + str(cur_table) + '.var_' + str(var_name)
                where_clause_ineqs.append(tmpstr)

            tmpstr = 'tab1.id = tab%d.id' % cur_table
            where_clause_ids.append(tmpstr)

        from_clause.append(new_table + ' as tab' + str(cur_table))

        query = 'create temporary table %s as select %s' % (
            cur_table_name, select_clause[0])
        for clause in select_clause[1:]:
            query += ', ' + clause

        query += ' from ' + from_clause[0]
        for clause in from_clause[1:]:
            query += ', ' + clause

        query += ' where ' + where_clause_ids[0]
        for clause in where_clause_ids[1:]:
            query += ' and ' + clause

        query += ' and ' + where_clause_ineqs[0]
        for clause in where_clause_ineqs[1:]:
            query += ' and ' + clause

#        print query
        db.execute(query)
        # db_conn.commit()

        print(db.query)

        if is_empty(db, cur_table_name):
            print('Table ' + cur_table_name + ' is empty')
            db.execute('drop table ' + cur_table_name)
            # db_conn.commit()
            print(db.query)
            return result

        cur_table_index[0] += 1
        cur_predicate = Predicate(predicate.name, predicate.arity, predicate.depth, hcb_utils.copy(
            cur_args), new_min, new_max, predicate.mode)
        print('Unroll output: ')
        cur_predicate.output()
        new_h = hcb_utils.copy(cur_hyp.h)
        new_h.append(cur_predicate)

        cur_hyp = Hypothesis(new_h, cur_table_name,
                             predicate.depth, new_min, new_max, mode_id)
        # print 'Unroll output: '
        cur_hyp.output()
        result.append(cur_hyp)
        cur_table += 1


def is_empty(db, table_name):
    stmt = 'select count(*) from ' + table_name
    db.execute(stmt)
    print(db.query)
    result = db.fetchall()

    answer = result[0][0] == 0
    return answer


def xjoin(db, hypothesis, predicate, mode_id, col_dict, cur_table_index,db_conn):
    #was commented
    print('xjoin hyp:')
    hypothesis.output()
    print('pred: ')
    predicate.output()
    print('')

    col_list = col_dict[predicate.name]
    where_clause = []
    select_clause = []
    has_output = False

    for i in range(len(predicate.args)):
        if predicate.mode.args[i] == 'output':
            if predicate.args[i] <= hypothesis.max_depth_var:
                where_clause.append(
                    hypothesis.t + '.var_' + str(predicate.args[i]) + '=' + predicate.name + '.' + col_list[i])
            elif predicate.args[i] not in predicate.args[:i]:
                select_clause.append(
                    predicate.name + '.' + col_list[i] + ' as var_' + str(predicate.args[i]))
                has_output = True
        else:
            where_clause.append(
                hypothesis.t + '.var_' + str(predicate.args[i]) + '=' + predicate.name + '.' + col_list[i])

    tbl_name = 'hyp_table_' + str(cur_table_index[0])
    stmt = 'create temporary table ' + tbl_name + ' as '
    stmt += ' select ' + hypothesis.t + '.*'
    for clause in select_clause:
        stmt += ', ' + clause

    stmt += ' from ' + hypothesis.t + ', ' + predicate.name
    stmt += ' where ' + where_clause[0]
    for clause in where_clause[1:]:
        stmt += ' and ' + clause

    # print("1",stmt)
    db.execute(stmt)
    print(db.query)
    # db_conn.commit()

    if is_empty(db, tbl_name):
        db.execute('drop table ' + tbl_name)
        print(db.query)
        # db_conn.commit()
        return []

    cur_table_index[0] += 1
    new_h = hcb_utils.copy(hypothesis.h)
    new_h.append(predicate)

    if has_output:
        result = unroll(db, new_h, tbl_name, predicate,
                        mode_id, cur_table_index,db_conn)
        return result

    new_min = hypothesis.min_depth_var
    new_max = max([predicate.max_var, hypothesis.max_depth_var])

    print('prev_hyp_depth: %d, pred_depth: %d, new_min: %d, new_max: %d' % (hypothesis.depth, predicate.depth, new_min, new_max))
    new_hypothesis = Hypothesis(
        new_h, tbl_name, predicate.depth, new_min, new_max, mode_id)
    return [new_hypothesis]
    # return None


def generateH(modes, target, db, seed_table, gamma, phi, depth_bound, length_bound, col_dict, bottom_clause,db_conn):
    init_hyp = Hypothesis([target], seed_table, 0,
                          target.min_var, target.max_var, 1)
    bottom_clause.insert(init_hyp, 0)

    openset = [(init_hyp, 1)]
    cur_table_index = [1]

    while (openset != []):
        cur_hyp_pair = gamma(openset)
        cur_hyp = cur_hyp_pair[0]
        cur_index = cur_hyp_pair[1]
        for mode_id in range(cur_hyp.mode_index, len(modes)):
            mode = modes[mode_id]
            if cur_hyp.valid_mode(mode):
                cur_extension = cur_hyp.get_first_extension(mode)
                while cur_extension != None:
                    #                    cur_extension.output()
                    next_hyps = xjoin(db, cur_hyp, cur_extension,
                                      mode_id, col_dict, cur_table_index,db_conn)
                    for next_hyp in next_hyps:
                        
                        if phi(next_hyp.t):
                            next_index = bottom_clause.insert(
                                next_hyp, cur_index)
                            if (next_hyp.depth <= depth_bound):
                                openset.append((next_hyp, next_index))
                            elif (len(next_hyp.h) <= length_bound):
                                openset.append((next_hyp, next_index))
                        else:
                            db.execute('drop table ' + next_hyp.t)
                            print(db.query)
                            # db_conn.commit()

                    cur_extension = cur_hyp.get_next_extension(
                        mode, cur_extension)

        db.execute('drop table ' + cur_hyp.t)
        print(db.query)
        # db_conn.commit()

    print('Space size: %d' % bottom_clause.hyp_count)

# end generateH()


def dummy_chooser(list):
    return list.pop(0)


def dummy_filter(db, hyp):
    if hyp is None:
        return False
    return True


def create_seed(db, table_name, arity, names, selection_clause, dbconn):
    seed_tbl_name = table_name + '_seed'

    db.execute("alter sequence seed_table_id restart with 1")
    print(db.query)

    column_names = range(arity)
    print("colnames", column_names)
    stmt = "create table if not exists " + seed_tbl_name + \
        " as select nextval(\'seed_table_id\') as id, " + \
        table_name + "."+names[0] + " as var_1"
 

    for i in column_names[1:]:
        stmt += ", " + table_name + "." + names[i] + " as var_" + (i+1)

    stmt += " from " + table_name + ", seed_table_id " + selection_clause
    # print(stmt)
    db.execute(stmt)
    print(db.query)
    db.execute("select * from " + seed_tbl_name)
    print(db.query)
    result = db.fetchall()
    # dbconn.commit()
    print(result)
    return seed_tbl_name


def get_seed_count(db, table):

    query = 'select count(distinct id) from ' + table
    db.execute(query)
    print(db.query)
    result = db.fetchall()
    num_seeds = result[0][0]
    print('Table seeds', table, num_seeds)
    return num_seeds


def init_filter(db, support, seed_table, dbconn):
    query = 'select count(id) from ' + seed_table
    db.execute(query)
    print(db.query)
    result = db.fetchall()
    total_seeds = result[0][0]
    threshold = total_seeds * support

    # dbconn.commit()
    print('Threshold will be %d seeds' % threshold)
    return lambda table: get_seed_count(db, table) >= threshold


def connect(db):
    db_conn = psycopg2.connect(
        "dbname = train_db password=gaurav user=postgres")
    print("connected to database")
    return db_conn
