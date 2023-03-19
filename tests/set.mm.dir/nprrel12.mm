include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wrel.mm"
include "brrelex12.mm"
include "mpan.mm"
include "con3i.mm"

theorem nprrel12
  let cA: class A
  let cB: class B
  let cR: class R
  assume nprrel12.1: |- Rel R


  assert |- ( -. ( A e. _V /\ B e. _V ) -> -. A R B )

  proof
    cA
    cB
    cR
    wbr
    #
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    cR
    wrel
    @0
    @1
    nprrel12.1
    cA
    cB
    cR
    brrelex12
    mpan
    con3i
end
