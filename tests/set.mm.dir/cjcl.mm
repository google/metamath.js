include "cc.mm"
include "ccj.mm"
include "cjf.mm"
include "ffvelrni.mm"

theorem cjcl
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. CC -> ( * ` A ) e. CC )

  proof
    cc
    cc
    cA
    ccj
    cjf
    ffvelrni
end
