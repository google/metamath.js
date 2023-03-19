include "cen.mm"
include "wrel.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "relen.mm"
include "brrelex12.mm"
include "mpan.mm"

theorem encv
  let cA: class A
  let cB: class B


  assert |- ( A ~~ B -> ( A e. _V /\ B e. _V ) )

  proof
    cen
    wrel
    cA
    cB
    cen
    wbr
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    relen
    cA
    cB
    cen
    brrelex12
    mpan
end
