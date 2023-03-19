include "wfo.mm"
include "fof.mm"
include "ffund.mm"

theorem fofun
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -onto-> B -> Fun F )

  proof
    cA
    cB
    cF
    wfo
    cA
    cB
    cF
    cA
    cB
    cF
    fof
    ffund
end
