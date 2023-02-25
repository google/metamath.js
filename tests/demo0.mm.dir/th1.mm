include "lexicon.mm"
include "tt.mm"
include "tze.mm"
include "tpl.mm"
include "weq.mm"
include "a2.mm"
include "wim.mm"
include "a1.mm"
include "mp.mm"

theorem th1
  let term t
  assert |- t = t
  proof
    0. tt(): term t
    1. tze(): term 0
    2. tpl(0,1): term ( t + 0 )
    3. tt(): term t
    4. weq(2,3): wff ( t + 0 ) = t
    5. tt(): term t
    6. tt(): term t
    7. weq(5,6): wff t = t
    8. tt(): term t
    9. a2(8): |- ( t + 0 ) = t
    10. tt(): term t
    11. tze(): term 0
    12. tpl(10,11): term ( t + 0 )
    13. tt(): term t
    14. weq(12,13): wff ( t + 0 ) = t
    15. tt(): term t
    16. tze(): term 0
    17. tpl(15,16): term ( t + 0 )
    18. tt(): term t
    19. weq(17,18): wff ( t + 0 ) = t
    20. tt(): term t
    21. tt(): term t
    22. weq(20,21): wff t = t
    23. wim(19,22): wff ( ( t + 0 ) = t -> t = t )
    24. tt(): term t
    25. a2(24): |- ( t + 0 ) = t
    26. tt(): term t
    27. tze(): term 0
    28. tpl(26,27): term ( t + 0 )
    29. tt(): term t
    30. tt(): term t
    31. a1(28,29,30): |- ( ( t + 0 ) = t -> ( ( t + 0 ) = t -> t = t ) )
    32. mp(14,23,25,31): |- ( ( t + 0 ) = t -> t = t )
    33. mp(4,7,9,32): |- t = t
end
