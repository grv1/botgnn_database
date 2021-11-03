#!/usr/bin/python

# utilities for permutation

def copy(ls):
    result = []
    for item in ls:
        result.append(item)

    return result

def permute_all(min_var, max_var, length):
    if length == 0:
        return []

    else:
        result = []
        tmp = permute_all(min_var,max_var,length-1)
        for i in range(min_var,max_var+1):
            cp = copy(tmp)
            result.append(cp.insert(0,i))

        return result


def main():
    print 'Hello'
    cp = copy([])
    tmp = []
    print cp.insert(0,1)
    print tmp.insert(0,1)
    print 
    print permute_all(1,1,0)
    print permute_all(1,1,1)
    
if __name__ == '__main__':
    main()
        



            
