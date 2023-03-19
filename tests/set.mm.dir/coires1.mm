include "ccnv.mm"
include "cres.mm"
include "cid.mm"
include "ccom.mm"
include "cocnvcnv1.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "coi1.mm"
include "ax-mp.mm"
include "eqtr3i.mm"
include "reseq1i.mm"
include "resco.mm"
include "rescnvcnv.mm"

theorem coires1
  let cA: class A
  let cB: class B


  assert |- ( A o. ( _I |` B ) ) = ( A |` B )

  proof
    cA
    ccnv
    #
    ccnv
    #
    cB
    cres
    #
    cA
    cid
    cB
    cres
    ccom
    #
    cA
    cB
    cres
    cA
    cid
    ccom
    #
    cB
    cres
    @2
    @3
    @4
    @1
    cB
    @1
    cid
    ccom
    #
    @4
    @1
    cA
    cid
    cocnvcnv1
    @1
    wrel
    @5
    @1
    wceq
    @0
    relcnv
    @1
    coi1
    ax-mp
    eqtr3i
    reseq1i
    cA
    cid
    cB
    resco
    eqtr3i
    cA
    cB
    rescnvcnv
    eqtr3i
end
