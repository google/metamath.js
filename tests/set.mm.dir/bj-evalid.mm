include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cslot.mm"
include "cfv.mm"
include "cvv.mm"
include "wceq.mm"
include "resiexg.mm"
include "bj-evalval.mm"
include "syl.mm"
include "fvresi.mm"
include "sylan9eq.mm"

theorem bj-evalid
  let cA: class A
  let cV: class V
  let cW: class W


  assert |- ( ( V e. W /\ A e. V ) -> ( Slot A ` ( _I |` V ) ) = A )

  proof
    cV
    cW
    wcel
    #
    cA
    cV
    wcel
    cid
    cV
    cres
    #
    cA
    cslot
    cfv
    #
    cA
    @1
    cfv
    #
    cA
    @0
    @1
    cvv
    wcel
    @2
    @3
    wceq
    cV
    cW
    resiexg
    cA
    @1
    cvv
    bj-evalval
    syl
    cV
    cA
    fvresi
    sylan9eq
end
