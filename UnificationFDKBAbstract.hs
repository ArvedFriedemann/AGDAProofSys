module UnificationFDKBAbstract where

--Main problem here: every implication technically runs on its own KB. This might become an issue for multi goal traversals...
--This way, every goal runs on its own kb. This allows to enhancing the KB during the search (needed for implications). Multigoals still work...communication via shared variables stays as is.
--Can goals in general also use each other? The should be in each others kbs...
proof :: [(State, KB, OpenTerm)] -> [(State, KB, OpenTerm)]
--when doing assignments outside, they can directly translate into the hypothesis. But the other way around cannot hold...assignments within the hypothesis cannot go back to the general assignments. This can be done with backtracking (so backtracking to the point after the implication was proven), however, then multiple goals could not be tackeled at once. 
