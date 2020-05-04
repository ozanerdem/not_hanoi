enum Blocks;
enum Pegs;
enum Levels;

% Supply a -D"T=<val>;" to the minizinc cmdline
% Actions will be taken at timesteps [0..T-1]
int : T;

%%%%%%%%%%%%%
% VARIABLES %
%%%%%%%%%%%%%

% Peg of block
array[Blocks, 0 .. T] of var Pegs : peg;
% Level of block
array[Blocks, 0 .. T] of var Levels : level;
% b1 is over b2
array[Blocks, Blocks, 0..T] of var bool : over;
% Block is blocked (weird.)
array[Blocks, 0..T] of var bool : blocked;
% Top block of peg is this block
array[Pegs, 0..T] of var Blocks : topblock;
% Move the block on peg
array[Blocks, Pegs, 0..T-1] of var bool : move;
% Block was moved
array[Blocks, 0..T-1] of var bool : moved;
% Action type 1: Move some block on top of the other one
array[Blocks, Pegs, 0..T-1] of var bool : move_to_block;
% Action type 2: Move some block to its "natural position" on a peg:
array[Blocks, Pegs, 0..T-1] of var bool : move_to_peg;
% Peg has some block(s) on it
array[Pegs, 0..T] of var bool : occupied;
% This is the level of a block when you put it on an empty peg.
% Think of a better name.
array[Blocks] of Levels : naturalposition = [level0, level1, level2, level3];


%%%%%%%%%%%%%%%%%
% INITIAL STATE %
%%%%%%%%%%%%%%%%%

constraint forall(b in Blocks)(
    % min(<enum>) is the first element of the enum
    peg[b, 0] = min(Pegs)
);
constraint forall(b in Blocks)(
    % Implicitly coerce block to enum, and explicitly coerce
    % it to a level
    level[b, 0] = to_enum(Levels, b)
);

%%%%%%%%%%%
% FLUENTS %
%%%%%%%%%%%

constraint forall(b1 in Blocks, b2 in Blocks, t in 0..T) (
    over[b1, b2, t] <-> peg[b1, t] = peg[b2, t] /\ level[b1,t] > level[b2,t]
);

constraint forall(t in 0..T, b in Blocks)(
    bool_clause_reif([over[other, b, t] | other in Blocks where b != other],
                     [],
                     blocked[b, t])
);

constraint forall(t in 0..T, p in Pegs)(
    bool_clause_reif([peg[b,t] == p | b in Blocks], [], occupied[p, t])
);

% This is not an equivalence, as topblock is only meaningful for
% occupied pegs
constraint forall(t in 0..T, p in Pegs, b in Blocks)(
    topblock[p, t] = b
        <-
    (peg[b, t] = p /\ not blocked[b, t]
));

%%%%%%%%%%%
% ACTIONS %
%%%%%%%%%%%

% Two types of moves
% (1) Destination has a block somewhere above the natural position
% (2) Destination does not have a block somewhere above the natural 
%      position. In this case, just place it in the natural position

% A macro action that combines the common characteristics of both kind
% of moves. Also nice to have when you're pretty printing at the end.
constraint forall(t in 0..T-1, b, top in Blocks, p in Pegs)(
    move[b, p, t] <-> move_to_peg[b, p, t] \/ move_to_block[b, p, t]
);

constraint forall(t in 0..T-1, b, tb, top in Blocks, p in Pegs)(
    move_to_peg[b, p, t] ->  not occupied[p, t] \/ 
                             (topblock[p, t] = tb /\
                              level[tb, t] < naturalposition[b])

);

constraint forall(t in 0..T-1, b in Blocks, p in Pegs)(
    move_to_peg[b, p, t] -> level[b, t + 1] = naturalposition[b]
);

constraint forall(t in 0..T-1, top, b in Blocks, p in Pegs)(
    move_to_block[b, p, t] /\ topblock[p, t] = top 
        ->
    level[b, t + 1] = level[top, t] + 1
);

constraint forall(t in 0..T-1, p in Pegs, b in Blocks)(
    move_to_block[b, p, t] -> occupied[p, t]
);

constraint forall(t in 0..T-1, p in Pegs, b, top in Blocks)(
    move_to_block[b, p, t] /\ top = topblock[p, t] 
        -> 
    naturalposition[b] <= level[top, t] + 1
);

constraint forall(t in 0..T-1, b in Blocks, p in Pegs)(
    move[b, p, t] -> peg[b, t] != p /\ peg[b, t + 1] = p /\ not blocked[b, t]
);

% Project the ternary move variable to the binary one
constraint forall(t in 0..T-1, b in Blocks)(
   bool_clause_reif([move[b, p, t] | p in Pegs], [], [moved[b,t]])
);

% Frame 
constraint forall(t in 0..T-1, b in Blocks)(
   not moved[b, t] <-> peg[b, t + 1] = peg[b, t] /\
                       level[b, t + 1] = level[b, t]
);

% Pick only one action
% TODO Does disjunctive make sense here?
constraint forall(t in 0..T-1, b in Blocks)(
    moved[b, t]
        ->
    forall(other_block in Blocks where b != other_block)(
        not moved[other_block, t])
);

%%%%%%%%
% GOAL %
%%%%%%%%

constraint peg[block0, T] = peg[block1, T];
constraint peg[block0, T] = peg[block2, T];
constraint peg[block0, T] = peg[block3, T];
constraint peg[block0, T] != peg0;

%%%%%%%%%%%%
% EPILOGUE %
%%%%%%%%%%%%

solve satisfy;

output [if fix(move[b, p, t]) then "Move \(b) to \(p) at \(t)\n" else ""
        endif | t in 0..T-1, b in Blocks, p in Pegs];
