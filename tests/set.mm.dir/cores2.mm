include "cdm.mm"
include "wss.mm"
include "ccnv.mm"
include "cres.mm"
include "ccom.mm"
include "crn.mm"
include "wceq.mm"
include "dfdm4.mm"
include "sseq1i.mm"
include "cores.mm"
include "sylbi.mm"
include "cnvco.mm"
include "cocnvcnv1.mm"
include "eqtri.mm"
include "3eqtr4g.mm"
include "cnveqd.mm"
include "wrel.mm"
include "relco.mm"
include "dfrel2.mm"
include "mpbi.mm"
include "3eqtr3g.mm"

theorem cores2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( dom A C_ C -> ( A o. `' ( `' B |` C ) ) = ( A o. B ) )

  proof
    cA
    cdm
    #
    cC
    wss
    #
    cA
    cB
    ccnv
    #
    cC
    cres
    #
    ccnv
    #
    ccom
    #
    ccnv
    #
    ccnv
    #
    cA
    cB
    ccom
    #
    ccnv
    #
    ccnv
    #
    @5
    @8
    @1
    @6
    @9
    @1
    @3
    cA
    ccnv
    #
    ccom
    #
    @2
    @11
    ccom
    #
    @6
    @9
    @1
    @11
    crn
    #
    cC
    wss
    @12
    @13
    wceq
    @0
    @14
    cC
    cA
    dfdm4
    sseq1i
    @2
    @11
    cC
    cores
    sylbi
    @6
    @4
    ccnv
    @11
    ccom
    @12
    cA
    @4
    cnvco
    @3
    @11
    cocnvcnv1
    eqtri
    cA
    cB
    cnvco
    3eqtr4g
    cnveqd
    @5
    wrel
    @7
    @5
    wceq
    cA
    @4
    relco
    @5
    dfrel2
    mpbi
    @8
    wrel
    @10
    @8
    wceq
    cA
    cB
    relco
    @8
    dfrel2
    mpbi
    3eqtr3g
end
