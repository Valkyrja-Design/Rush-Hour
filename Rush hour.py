from z3 import *
import sys

counter = 0

# For sum to one condition
def sum_to_one( ls ):
    global counter 
    counter += 1
    cond1 = Or(ls)
    s=[Bool(f"a_{t}_{counter}") for t in range(len(ls))]
    and_list=[]
    and_list.append(Or(Not(ls[0]), s[0]))
    for i in range(1,len(ls)-1):
        and_list.append(And(Implies(Or(ls[i],s[i-1]),s[i]),Implies(s[i-1], Not(ls[i]))))
    and_list.append(Implies(s[len(ls)-2],Not(ls[len(ls)-1])))
    
    cond2 = And(and_list)
    return And(cond1, cond2)

# Get size of board and max number of moves
n, limit = 0, 0


# Get location of red car
x, y = 0, 0

mines = []

# Vertical and horizontal cars
vcars = []
hcars = []

# Get input for mines and other cars
linen = 0
with open(sys.argv[1]) as f:
    for line in f:
        if (linen == 0):
            # Get size of board and max number of moves
            n, limit = map(int, line.strip().split(","))
            linen += 1
        elif (linen == 1):
            # Get location of red car
            x, y = map(int, line.strip().split(","))
            linen +=1
        else:
            tu = [0]*3
            tu[0], tu[1], tu[2] = map(int, line.strip().split(","))
            # Mine
            if (tu[0] == 2):
                mines.append([tu[1], tu[2]])
            else:
                if (tu[0] == 1):
                    hcars.append([tu[1], tu[2]])
                else:
                    vcars.append([tu[1], tu[2]])

limit = limit+1

# The position the red car is at, r_10 means x coordinate of red car at state 1 while r_11 is the y coordinate
red = [[Int(f"r_{s}_{j}") for j in range(2)] for s in range(limit)]

# Storing the invariants like mine locations and bounds on Ints
F = []
for r in red:
    F.append(And(0<= r[0], r[1] < n-1, 0<=r[1], r[0]<n))

# List containing the position constants of horizontal, vertical cars and mines resp 
hothers = [[[Int(f"h_{i+1}_{s}_{j}") for j in range(2)] for i in range(len(hcars))] for s in range(limit)]
vothers = [[[Int(f"v_{i+1}_{s}_{j}") for j in range(2)] for i in range(len(vcars))] for s in range(limit)]
ms = [[[Int(f"m_{i+1}_{s}_{j}") for j in range(2)] for i in range(len(mines))] for s in range(limit)]

# Add mine locations
for s in range(limit):
    for i in range(len(mines)):
        F.append(And(ms[s][i][0] == mines[i][0], ms[s][i][1] == mines[i][1]))

# print(ms[0][0]+1)
# print(F)

initial_state = []
states = [[] for _ in range(limit)]

# Initial position of red car
initial_state.append(And(red[0][0] == x, red[0][1] == y))

# States of the game
win_states = [Bool(f"s_{t}") for t in range(limit)]

# Moves of each car stored according to the order red-vcars-hcars
moves = [[Bool(f"mov_{car+1}_{s}") for car in range(1+len(vcars)+len(hcars))] for s in range(limit)]

# Direction to move in
dir = [[Bool(f"d_{i}_{s}") for i in range(2)] for s in range(limit)]

# Booleans specifying the moves taken each round (has bugs!)
winmoves = [[[Bool(f"win_{dr}_{car+1}_{s}") for dr in range(2)] for car in range(1+len(vcars)+len(hcars))] for s in range(limit)]

# Add initial state constraints of vcars, hcars and mines
for i in range(len(hcars)):
    F.append(And(hothers[0][i][0] >=0, hothers[0][i][0]<n))
    F.append(And(hothers[0][i][1] >=0, hothers[0][i][1]<n-1))
    hcar = hcars[i]
    x_ = hcar[0]
    y_ = hcar[1]
    initial_state.append(And(hothers[0][i][0] == x_, hothers[0][i][1] == y_))

for i in range(len(vcars)):
    F.append(And(vothers[0][i][0] >=0, vothers[0][i][0]<n-1))
    F.append(And(vothers[0][i][1] >=0, vothers[0][i][1]<n))
    vcar = vcars[i]
    x_ = vcar[0]
    y_ = vcar[1]
    initial_state.append(And(vothers[0][i][0] == x_, vothers[0][i][1] == y_))

for i in range(limit):
    state = states[i]
    state.append(Implies(win_states[i], red[i][1] == n-2))

# Only one state can be winning
# one_win_state = sum_to_one(win_states)

# Logic specifying how transitions from s_i to s_{i+1} are related
def transition(st):

    #Pick the car to move
    pick = sum_to_one(moves[st])
    #Pick a direction
    pickdir = sum_to_one(dir[st])
    transition_state = []
    transition_state += [pick, pickdir]

    # The possible moves
    mymoves = []

    # Iterate over all cars 
    for i in range(1+len(vcars)+len(hcars)):

        # If we chose to move Red car
        if (i==0):
            move = []
            
            # dir[st][0] means move right at state st
            # Check if movement possible by using free(), if yes then map the position constants of next state according to the move
            # Positions of other cars remain same, just change position of red car
            # If movement not possible return False
            move.append(If(And(dir[st][0], moves[st][0], free(red[st][0], red[st][1]+2, st), red[st][1]+2<n), And(
                [ hothers[st+1][h][0] == hothers[st][h][0] for h in range(len(hcars))] +
                [ vothers[st+1][h][0] == vothers[st][h][0] for h in range(len(vcars))] + 
                [ hothers[st+1][h][1] == hothers[st][h][1] for h in range(len(hcars))] +
                [ vothers[st+1][h][1] == vothers[st][h][1] for h in range(len(vcars))] + 
                [red[st+1][0] == red[st][0], red[st+1][1] == red[st][1]+1] +
                # Add constraint such that only winmove of this car is true
                [winmoves[st][j][k] if (j==i and k==0) else Not(winmoves[st][j][k]) for k in range(2) for j in range(1+len(vcars)+len(hcars))]
            ), False))

            # Move left
            move.append(If(And(dir[st][1], moves[st][0], free(red[st][0], red[st][1]-1, st), red[st][1]-1>=0), And(
                [ hothers[st+1][h][0] == hothers[st][h][0] for h in range(len(hcars))] +
                [ vothers[st+1][h][0] == vothers[st][h][0] for h in range(len(vcars))] + 
                [ hothers[st+1][h][1] == hothers[st][h][1] for h in range(len(hcars))] +
                [ vothers[st+1][h][1] == vothers[st][h][1] for h in range(len(vcars))] + 
                [red[st+1][0] == red[st][0], red[st+1][1] == red[st][1]-1] +
                [winmoves[st][j][k] if (j==i and k==1) else Not(winmoves[st][j][k]) for k in range(2) for j in range(1+len(vcars)+len(hcars))]
            ), False))
            mymoves += move

        # If we move a vertical car
        elif (i>0 and i<1+len(vcars)):
            move = []

            # Check for free cell and move and set constants of this car in next state, everything else is same
            move.append(If(And(dir[st][0], moves[st][i], free(vothers[st][i-1][0]-1, vothers[st][i-1][1], st), vothers[st][i-1][0]-1>=0),
            And(
                [vothers[st+1][h][0] == vothers[st][h][0] if (h!=i-1) else vothers[st+1][h][0] == vothers[st][h][0]-1 for h in range(len(vcars))] +
                [vothers[st+1][h][1] == vothers[st][h][1] for h in range(len(vcars))] +
                [hothers[st+1][h][0] == hothers[st][h][0] for h in range(len(hcars))] +
                [hothers[st+1][h][1] == hothers[st][h][1] for h in range(len(hcars))] +
                [red[st+1][0] == red[st][0], red[st+1][1] == red[st][1]] +
                [winmoves[st][j][k] if (j==i and k==0) else Not(winmoves[st][j][k]) for k in range(2) for j in range(1+len(vcars)+len(hcars))]
            ), False))
            move.append(If(And(dir[st][1], moves[st][i], free(vothers[st][i-1][0]+2, vothers[st][i-1][1], st), vothers[st][i-1][0]+2<n),
            And(
                [vothers[st+1][h][0] == vothers[st][h][0] if (h!=i-1) else vothers[st+1][h][0] == vothers[st][h][0]+1 for h in range(len(vcars))] +
                [vothers[st+1][h][1] == vothers[st][h][1] for h in range(len(vcars))] +
                [hothers[st+1][h][0] == hothers[st][h][0] for h in range(len(hcars))] +
                [hothers[st+1][h][1] == hothers[st][h][1] for h in range(len(hcars))] +
                [red[st+1][0] == red[st][0], red[st+1][1] == red[st][1]] +
                [winmoves[st][j][k] if (j==i and k==1) else Not(winmoves[st][j][k]) for k in range(2) for j in range(1+len(vcars)+len(hcars))]
            ), False))
            mymoves += move

        # Moving a horizontal car
        else:
            move = []
            move.append(If(And(dir[st][0], moves[st][i], free(hothers[st][i-1-len(vcars)][0], hothers[st][i-1-len(vcars)][1]+2, st), hothers[st][i-1-len(vcars)][1]+2<n),
            And(
                [hothers[st+1][h][1] == hothers[st][h][1] if (h!=i-1-len(vcars)) else hothers[st+1][h][1] == hothers[st][h][1]+1 for h in range(len(hcars))] +
                [hothers[st+1][h][0] == hothers[st][h][0] for h in range(len(hcars))] +
                [vothers[st+1][h][0] == vothers[st][h][0] for h in range(len(vcars))] +
                [vothers[st+1][h][1] == vothers[st][h][1] for h in range(len(vcars))] +
                [red[st+1][0] == red[st][0], red[st+1][1] == red[st][1]] +
                [winmoves[st][j][k] if (j==i and k==0) else Not(winmoves[st][j][k]) for k in range(2) for j in range(1+len(vcars)+len(hcars))]
            ), False))
            move.append(If(And(dir[st][1], moves[st][i], free(hothers[st][i-1-len(vcars)][0], hothers[st][i-1-len(vcars)][1]-1, st), hothers[st][i-1-len(vcars)][1]-1>=0),
            And(
                [hothers[st+1][h][1] == hothers[st][h][1] if (h!=i-1-len(vcars)) else hothers[st+1][h][1] == hothers[st][h][1]-1 for h in range(len(hcars))] +
                [hothers[st+1][h][0] == hothers[st][h][0] for h in range(len(hcars))] +
                [vothers[st+1][h][0] == vothers[st][h][0] for h in range(len(vcars))] +
                [vothers[st+1][h][1] == vothers[st][h][1] for h in range(len(vcars))] +
                [red[st+1][0] == red[st][0], red[st+1][1] == red[st][1]] +
                [winmoves[st][j][k] if (j==i and k==1) else Not(winmoves[st][j][k]) for k in range(2) for j in range(1+len(vcars)+len(hcars))]
            ), False))
            mymoves += move
    
    # In case no car can be moved set the constants in next state to be same as this state
    transition_state.append(If(Or(mymoves), Or(mymoves), And(
        [hothers[st+1][h][1] == hothers[st][h][1] for h in range(len(hcars))] +
        [hothers[st+1][h][0] == hothers[st][h][0] for h in range(len(hcars))] +
        [vothers[st+1][h][0] == vothers[st][h][0] for h in range(len(vcars))] +
        [vothers[st+1][h][1] == vothers[st][h][1] for h in range(len(vcars))] +
        [red[st+1][0] == red[st][0], red[st+1][1] == red[st][1]]
    )))

    return And(transition_state)

# Function to check if a given cell is free 
def free(X, Y, st):
    cond = []

    # Check if red car occupies it
    freer = Not(And(red[st][1]<=Y, Y < red[st][1]+2, X == red[st][0]))
    cond.append(freer)

    # Check for mines, vcars and hcars similarly
    for i in range(len(vcars)):
        xc = vothers[st][i][0]
        yc = vothers[st][i][1]
        cond.append(Not(And(Y == yc, xc <= X, X < xc+2)))
    
    for i in range(len(hcars)):
        xc = hothers[st][i][0]
        yc = hothers[st][i][1]
        cond.append(Not(And(X == xc, yc <= Y, Y < yc+2)))
    
    for i in range(len(mines)):
        xc = ms[st][i][0]
        yc = ms[st][i][1]
        cond.append(Not(And(Y==yc, X==xc)))
    
    return And(cond)

# Add initial_state and only one winning state constraint 
F.append(And(initial_state))
# F.append(one_win_state)
Possible = []

Possible.append(If(win_states[0], red[0][1] == n-2, False))
s = Solver()

flag = False

# Transition upto limit
for i in range(limit-1):

    Possible.append(If(win_states[i+1], red[i+1][1] == n-2, False))
    F.append(transition(i))
    F.append(Or(Possible))
    F.append(sum_to_one(win_states[:i+1]))
    s.push()
    s.add(And(F))
    result = s.check()
    # print(result)
    if (result == sat):
        flag = True
        m = s.model()
        # print(m)
        # Iterate over winmoves list
        for st in range(i+1):
            for i in range(1+len(vcars)+len(hcars)):
                if (i==0):
                    # If this was a winning move
                    if (is_true(m[winmoves[st][i][0]])):
                        # Get x and y positions under the model at this state
                        currx = m[red[st][0]]
                        curry = m[red[st][1]]
                        print(f"{currx},{simplify(curry+1)}")
                    elif (is_true(m[winmoves[st][i][1]])):
                        currx = m[red[st][0]]
                        curry = m[red[st][1]]
                        print(f"{currx},{curry}")
                elif (i>0 and i<1+len(vcars)):
                    if (is_true(m[winmoves[st][i][0]])):
                        currx = m[vothers[st][i-1][0]]
                        curry = m[vothers[st][i-1][1]]
                        print(f"{currx},{curry}")
                    elif (is_true(m[winmoves[st][i][1]])):
                        currx = m[vothers[st][i-1][0]]
                        curry = m[vothers[st][i-1][1]]
                        print(f"{simplify(currx+1)},{curry}")
                else:
                    if (is_true(m[winmoves[st][i][0]])):
                        currx = m[hothers[st][i-1-len(vcars)][0]]
                        curry = m[hothers[st][i-1-len(vcars)][1]]
                        print(f"{currx},{simplify(curry+1)}")
                    elif (is_true(m[winmoves[st][i][1]])):
                        currx = m[hothers[st][i-1-len(vcars)][0]]
                        curry = m[hothers[st][i-1-len(vcars)][1]]
                        print(f"{currx},{curry}")
        
        break
    s.pop()
    F.pop()
    F.pop()


if (flag == False):
    print("unsat")

# Winning condition at each state is that red car should be at y==n-2

# for s in range(limit):
#     Possible.append(If(win_states[s], red[s][1] == n-2, False))

# Add up all constraints and check
# F.append(Or(Possible))
# s = Solver()
# s.add(And(F))
# result = s.check()
# # print(s)
# print(result)

# ans = []
# if (result == sat):
#     m = s.model()
#     # print(m)

#     # Iterate over winmoves list
#     for st in range(limit):
#         for i in range(1+len(vcars)+len(hcars)):
#             if (i==0):

#                 # If this was a winning move
#                 if (is_true(m[winmoves[st][i][0]])):
#                     # Get x and y positions under the model at this state
#                     currx = m[red[st][0]]
#                     curry = m[red[st][1]]
#                     print(f"{currx},{simplify(curry+1)}")
#                 elif (is_true(m[winmoves[st][i][1]])):
#                     currx = m[red[st][0]]
#                     curry = m[red[st][1]]
#                     print(f"{currx},{curry}")
#             elif (i>0 and i<1+len(vcars)):
#                 if (is_true(m[winmoves[st][i][0]])):
#                     currx = m[vothers[st][i-1][0]]
#                     curry = m[vothers[st][i-1][1]]
#                     print(f"{currx},{curry}")
#                 elif (is_true(m[winmoves[st][i][1]])):
#                     currx = m[vothers[st][i-1][0]]
#                     curry = m[vothers[st][i-1][1]]
#                     print(f"{simplify(currx+1)},{curry}")
#             else:
#                 if (is_true(m[winmoves[st][i][0]])):
#                     currx = m[hothers[st][i-1-len(vcars)][0]]
#                     curry = m[hothers[st][i-1-len(vcars)][1]]
#                     print(f"{currx},{simplify(curry+1)}")
#                 elif (is_true(m[winmoves[st][i][1]])):
#                     currx = m[hothers[st][i-1-len(vcars)][0]]
#                     curry = m[hothers[st][i-1-len(vcars)][1]]
#                     print(f"{currx},{curry}")


'''
6,11
2,1
0,1,3
0,2,5
1,3,2
2,0,3
2,3,1
'''                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         