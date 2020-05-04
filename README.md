# not_hanoi

Solves the problem "We're Not in Hanoi Anymore" from [AoPS Online](https://artofproblemsolving.com/keeplearning).

Usage:
```
minizinc --solver chuffed -D"T=<t>" hanoi.mzn hanoi.dzn
```
to solve in `<t>` timesteps with `chuffed`. Tested only with `chuffed`. So far only considers 4 pegs, however can be easily generalized by replacing the data file.
