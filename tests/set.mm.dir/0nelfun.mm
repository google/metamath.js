include "wfun.mm"
include "wrel.mm"
include "c0.mm"
include "wnel.mm"
include "funrel.mm"
include "0nelrel.mm"
include "syl.mm"

theorem 0nelfun
  let cR: class R


  assert |- ( Fun R -> (/) e/ R )

  proof
    cR
    wfun
    cR
    wrel
    c0
    cR
    wnel
    cR
    funrel
    cR
    0nelrel
    syl
end
