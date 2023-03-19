include "wcel.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "cslot.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "bj-evalid.mm"
include "fveq2d.mm"
include "3adant3.mm"
include "bj-evalval.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"

theorem bj-evalidval
  let cA: class A
  let cU: class U
  let cF: class F
  let cV: class V
  let cW: class W


  assert |- ( ( V e. W /\ A e. V /\ F e. U ) -> ( F ` ( Slot A ` ( _I |` V ) ) ) = ( Slot A ` F ) )

  proof
    cV
    cW
    wcel
    #
    cA
    cV
    wcel
    #
    cF
    cU
    wcel
    #
    w3a
    cid
    cV
    cres
    cA
    cslot
    #
    cfv
    #
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cF
    @3
    cfv
    #
    @0
    @1
    @5
    @6
    wceq
    @2
    @0
    @1
    wa
    @4
    cA
    cF
    cA
    cV
    cW
    bj-evalid
    fveq2d
    3adant3
    @2
    @0
    @6
    @7
    wceq
    @1
    @2
    @7
    @6
    cA
    cF
    cU
    bj-evalval
    eqcomd
    3ad2ant3
    eqtrd
end
