include "tze.mm"
include "tpl.mm"
include "weq.mm"
include "a2.mm"
include "wim.mm"
include "a1.mm"
include "mp.mm"

theorem th1
  let tt: term t

  assert |- t = t

  step 0) tt(): term t
  step 1) tze(): term 0
  step 2) tpl(0,1): term ( t + 0 )
  step 3) tt(): term t
  step 4) weq(2,3): wff ( t + 0 ) = t
  step 5) tt(): term t
  step 6) tt(): term t
  step 7) weq(5,6): wff t = t
  step 8) tt(): term t
  step 9) a2(8): |- ( t + 0 ) = t
  step 10) tt(): term t
  step 11) tze(): term 0
  step 12) tpl(10,11): term ( t + 0 )
  step 13) tt(): term t
  step 14) weq(12,13): wff ( t + 0 ) = t
  step 15) tt(): term t
  step 16) tze(): term 0
  step 17) tpl(15,16): term ( t + 0 )
  step 18) tt(): term t
  step 19) weq(17,18): wff ( t + 0 ) = t
  step 20) tt(): term t
  step 21) tt(): term t
  step 22) weq(20,21): wff t = t
  step 23) wim(19,22): wff ( ( t + 0 ) = t -> t = t )
  step 24) tt(): term t
  step 25) a2(24): |- ( t + 0 ) = t
  step 26) tt(): term t
  step 27) tze(): term 0
  step 28) tpl(26,27): term ( t + 0 )
  step 29) tt(): term t
  step 30) tt(): term t
  step 31) a1(28,29,30): |- ( ( t + 0 ) = t -> ( ( t + 0 ) = t -> t = t ) )
  step 32) mp(14,23,25,31): |- ( ( t + 0 ) = t -> t = t )
  step 33) mp(4,7,9,32): |- t = t
end
