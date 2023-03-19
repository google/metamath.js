include "cc.mm"
include "ccos.mm"
include "cosf.mm"
include "ffvelrni.mm"

theorem coscl
  let cA: class A


  assert |- ( A e. CC -> ( cos ` A ) e. CC )

  proof
    cc
    cc
    cA
    ccos
    cosf
    ffvelrni
end
