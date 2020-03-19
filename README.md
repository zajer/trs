# Tracking_bigraph
An addon to the OCaml library "Bigraph". It allows tracking of nodes between state transitions.

## Credits
This is just an addon. 
It wouldn't work if not for the original library available here: https://bitbucket.org/mseve/bigraph

## Usage

Define an initial state of the system you want to examine:
``` 
let init_state_to_parse = 
"
{(0, A:1),(1, B:0),(2, B:0),(3, A:1)}
0 4 0
0110
0000
0000
0000
({}, {}, {(0, 1), (3, 1)})
"
let init_state = Big.of_string init_state_to_parse
```

Define both sides of a tracking reaction rule for your system:
```
let lhs_to_parse =
"
{(0, A:1),(1, B:0),(2, A:1)}
0 3 2
01010
00000
00001
({}, {}, {(0, 1), (2, 1)})
"
let rhs_to_parse =
"
{(0, A:1),(1, B:0),(2, A:1)}
0 3 2
00010
00000
01001
({}, {}, {(0, 1), (2, 1)})
"
let lhs = Big.of_string lhs_to_parse
let rhs = Big.of_string rhs_to_parse
```
Define a residue mapping for your reaction rule:
```
let res_map = Fun.empty |> Fun.add 0 0 |> Fun.add 1 1 |> Fun.add 2 2
```
Create a tracking reaction rule out of the components:
```
let rule = TBrs.parse_react "move" ~lhs ~rhs ~f_sm:None ~f_rnm:res_map
```
Set up a number of cores you want to utilize for the state space exploration:
```
Parmap.set_default_ncores 4
```
Launch exploration of the state space: 
```
let transitions,checked_states,unchecked_states,used_steps = TBrs.parexplore_ss ~s0:init_state ~rules:[rule] ~max_steps:777;;
```

Additionally you can save your results as a csv file:
```
RExp.export_ss_csv transitions (checked_states@unchecked_states)
```

The above example and others are available in the *examples* folder.

