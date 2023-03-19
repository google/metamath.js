include "wrel.mm"
include "ccnv.mm"
include "wceq.mm"
include "cid.mm"
include "ccom.mm"
include "dfrel2.mm"
include "cnvco.mm"
include "relcnv.mm"
include "coi1.mm"
include "ax-mp.mm"
include "cnveqi.mm"
include "eqtr3i.mm"
include "cnvi.mm"
include "coeq2.mm"
include "coeq1.mm"
include "sylan9eq.mm"
include "mpan2.mm"
include "id.mm"
include "3eqtr3a.mm"
include "sylbi.mm"

theorem coi2
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Rel A -> ( _I o. A ) = A )

  proof
    cA
    wrel
    cA
    ccnv
    #
    ccnv
    #
    cA
    wceq
    #
    cid
    cA
    ccom
    #
    cA
    wceq
    cA
    dfrel2
    @2
    cid
    ccnv
    #
    @1
    ccom
    #
    @1
    @3
    cA
    @0
    cid
    ccom
    #
    ccnv
    @5
    @1
    @0
    cid
    cnvco
    @6
    @0
    @0
    wrel
    @6
    @0
    wceq
    cA
    relcnv
    @0
    coi1
    ax-mp
    cnveqi
    eqtr3i
    @2
    @4
    cid
    wceq
    #
    @5
    @3
    wceq
    cnvi
    @2
    @7
    @5
    @4
    cA
    ccom
    @3
    @1
    cA
    @4
    coeq2
    @4
    cid
    cA
    coeq1
    sylan9eq
    mpan2
    @2
    id
    3eqtr3a
    sylbi
end
