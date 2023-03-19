include "wrel.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "brrelex2.mm"
include "mpan.mm"

theorem brrelex2i
  let cA: class A
  let cB: class B
  let cR: class R
  assume brrelexi.1: |- Rel R


  assert |- ( A R B -> B e. _V )

  proof
    cR
    wrel
    cA
    cB
    cR
    wbr
    cB
    cvv
    wcel
    brrelexi.1
    cA
    cB
    cR
    brrelex2
    mpan
end
