#!/usr/bin/python

import sys
import wild_gen

def get_bc():
    db = wild_gen.connect('pqr')

    modes = []
    modes.append(wild_gen.Mode(1,'p',1,[('output','any')]))
    modes.append(wild_gen.Mode(-1,'q',2,[('input','any'),('output','any')]))
    modes.append(wild_gen.Mode(1,'r1',1,[('input','any')]))
    modes.append(wild_gen.Mode(1,'r2',1,[('input','any')]))
    modes.append(wild_gen.Mode(1,'r3',1,[('input','any')]))
    modes.append(wild_gen.Mode(1,'r4',1,[('input','any')]))

    columns = dict()
    columns['p'] = ['X']
    columns['q'] = ['X','Y']
    columns['r1'] = ['X']
    columns['r2'] = ['X']
    columns['r3'] = ['X']
    columns['r4'] = ['X']

    #name, arity, depth, args, min, max, mode
    target = wild_gen.Predicate('p',1,0,[1],1,1,modes[0])

#    selection_clause = 'where X=\'x\''
    selection_clause = ''
    seed_table = wild_gen.create_seed(db,'p',1,['x'],selection_clause)

    gamma = wild_gen.dummy_chooser

    threshold=1
    phi = wild_gen.init_filter(db,threshold,seed_table)

#    bc = wild_gen.BC_Builder()
    bc = wild_gen.BC_Printer()

    wild_gen.generateH(modes, target, db, seed_table, gamma, phi, 2, 8, columns, bc)

    return bc

def main():
    bc = get_bc()
#    bc.output_aleph_bc('pqr_bc.yap')

if __name__ == "__main__":
    main()
