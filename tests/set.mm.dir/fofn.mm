include "wfo.mm"
include "fof.mm"
include "ffnd.mm"

theorem fofn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( F : A -onto-> B -> F Fn A )

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
    ffnd
end
