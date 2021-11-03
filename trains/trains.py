#!/usr/bin/python

# import sys
# # sys.path.insert(1,'D:/code/DOP/Users/hcorrada_old/Projects/ilp_05.tmp/python/wild_gen.py')
import wild_gen
import sys
sys.path.append('../')


def main():
    # create a connection to database #
    back_db = wild_gen.connect('trains')
    db_cursor = back_db.cursor()


#    back_db = pg.connect(dbname='trains')
#    scratch_db = pg.connect(dbname='train_scratch')
    #back_db = None
    #scratch_db = None

    # set mode definitions #
    modes = []
    modes.append(wild_gen.Mode(-1, 'has_car', 2, ['input', 'output']))
    modes.append(wild_gen.Mode(1, 'long', 1, ['input']))
    modes.append(wild_gen.Mode(1, 'short', 1, ['input']))
    modes.append(wild_gen.Mode(1, 'open', 1, ['input']))
    modes.append(wild_gen.Mode(1, 'closed', 1, ['input']))
    modes.append(wild_gen.Mode(1, 'double', 1, ['input']))
    modes.append(wild_gen.Mode(1, 'jagged', 1, ['input']))
#    modes.append(Mode(1,'shape',2,['input','const']))
 #   modes.append(Mode(1,'load',3,['input','const','const']))
  #  modes.append(Mode(1,'wheels',2,['input','const']))
   # modes.append(Mode(1,'infront',2,['input','input']))

    # set up column name dictionary #
    columns = dict()
    columns['has_car'] = ['train', 'car']
    columns['long'] = ['car']
    columns['short'] = ['car']
    columns['open'] = ['car']
    columns['closed'] = ['car']
    columns['double'] = ['car']
    columns['jagged'] = ['car']

    # set up target predicate #
    #name, arity, depth, args, min, max, mode
    target = wild_gen.Predicate('eastbound', 1, 0, [1], 1, 1, None)

    # set up seed table #
#    selection_clause = 'where train=\'east1\' or train=\'east5\''
    selection_clause = ''
    print(back_db)
    seed_table = wild_gen.create_seed(db_cursor, 'eastbound', 1, [
                                      'train'], selection_clause, back_db)
    back_db.commit()
    # set up choose function #
    gamma = wild_gen.dummy_chooser
    back_db.commit()
    # set up filter function #
    #phi = dummy_filter
    threshold = 1
    print("seedtable", seed_table)
    phi = wild_gen.init_filter(db_cursor, threshold, seed_table, back_db)
    back_db.commit()
    # set up bottom clause #
#    bc = wild_gen.BC_Printer()
    bc = wild_gen.BottomClause()
    print("bottom clause", bc)
    # run generateH #
    wild_gen.generateH(modes, target, db_cursor, seed_table,
                       gamma, phi, 2, 12, columns, bc,back_db)
    back_db.commit()
# end main()


if __name__ == '__main__':
    main()
