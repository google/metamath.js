include "wrel.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "brrelex.mm"
include "mpan.mm"

theorem brrelexi
  let cA: class A
  let cB: class B
  let cR: class R
  assume brrelexi.1: |- Rel R


  assert |- ( A R B -> A e. _V )

  proof
    cR
    wrel
    cA
    cB
    cR
    wbr
    cA
    cvv
    wcel
    brrelexi.1
    cA
    cB
    cR
    brrelex
    mpan
end
