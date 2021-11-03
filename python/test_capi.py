def multiply(a,b):
    print 'Will compute', a, 'times', b
    c = 0
    for i in range(a):
        c = c + b
    return c

if __name__ == "__main__":
    print multiply(2,3)
