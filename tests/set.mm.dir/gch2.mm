include "cgch.mm"
include "cvv.mm"
include "wceq.mm"
include "cale.mm"
include "crn.mm"
include "wss.mm"
include "ssv.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "cv.mm"
include "wcel.mm"
include "ccrd.mm"
include "cfv.mm"
include "com.mm"
include "wo.mm"
include "cun.mm"
include "cardidm.mm"
include "iscard3.mm"
include "mpbi.mm"
include "elun.mm"
include "wi.mm"
include "cfn.mm"
include "fingch.mm"
include "nnfi.mm"
include "sseldi.mm"
include "a1i.mm"
include "ssel.mm"
include "jaod.mm"
include "mpi.mm"
include "cdm.mm"
include "cen.mm"
include "wbr.mm"
include "wb.mm"
include "vex.mm"
include "wac.mm"
include "cpw.mm"
include "con0.mm"
include "wral.mm"
include "wa.mm"
include "csuc.mm"
include "alephon.mm"
include "simpr.mm"
include "simpl.mm"
include "wfn.mm"
include "alephfnon.mm"
include "fnfvelrn.mm"
include "sylancr.mm"
include "sseldd.mm"
include "suceloni.mm"
include "adantl.mm"
include "gchaleph2.mm"
include "syl3anc.mm"
include "isnumi.mm"
include "ralrimiva.mm"
include "dfac12.mm"
include "sylibr.mm"
include "dfac10.mm"
include "sylib.mm"
include "syl5eleqr.mm"
include "cardid2.mm"
include "engch.mm"
include "3syl.mm"
include "mpbid.mm"
include "2thd.mm"
include "eqrdv.mm"
include "impbii.mm"

theorem gch2
  let vx: setvar x


  assert |- ( GCH = _V <-> ran aleph C_ GCH )

  proof
    cgch
    cvv
    wceq
    #
    cale
    crn
    #
    cgch
    wss
    #
    @0
    @2
    @1
    cvv
    wss
    @1
    ssv
    cgch
    cvv
    @1
    sseq2
    mpbiri
    @2
    vx
    cgch
    cvv
    @2
    vx
    cv
    #
    cgch
    wcel
    #
    @3
    cvv
    wcel
    #
    @2
    @3
    ccrd
    cfv
    #
    cgch
    wcel
    #
    @4
    @2
    @6
    com
    wcel
    #
    @6
    @1
    wcel
    #
    wo
    #
    @7
    @6
    com
    @1
    cun
    wcel
    #
    @10
    @6
    ccrd
    cfv
    @6
    wceq
    @11
    @3
    cardidm
    @6
    iscard3
    mpbi
    @6
    com
    @1
    elun
    mpbi
    @2
    @8
    @7
    @9
    @8
    @7
    wi
    @2
    @8
    cfn
    cgch
    @6
    fingch
    @6
    nnfi
    sseldi
    a1i
    @1
    cgch
    @6
    ssel
    jaod
    mpi
    @2
    @3
    ccrd
    cdm
    #
    wcel
    @6
    @3
    cen
    wbr
    @7
    @4
    wb
    @2
    @3
    cvv
    @12
    vx
    vex
    #
    @2
    wac
    @12
    cvv
    wceq
    @2
    @3
    cale
    cfv
    #
    cpw
    #
    @12
    wcel
    #
    vx
    con0
    wral
    wac
    @2
    @16
    vx
    con0
    @2
    @3
    con0
    wcel
    #
    wa
    #
    @3
    csuc
    #
    cale
    cfv
    #
    con0
    wcel
    @20
    @15
    cen
    wbr
    #
    @16
    @19
    alephon
    @18
    @17
    @14
    cgch
    wcel
    @20
    cgch
    wcel
    @21
    @2
    @17
    simpr
    #
    @18
    @1
    cgch
    @14
    @2
    @17
    simpl
    #
    @18
    cale
    con0
    wfn
    #
    @17
    @14
    @1
    wcel
    alephfnon
    @22
    con0
    @3
    cale
    fnfvelrn
    sylancr
    sseldd
    @18
    @1
    cgch
    @20
    @23
    @18
    @24
    @19
    con0
    wcel
    #
    @20
    @1
    wcel
    alephfnon
    @17
    @25
    @2
    @3
    suceloni
    adantl
    con0
    @19
    cale
    fnfvelrn
    sylancr
    sseldd
    @3
    gchaleph2
    syl3anc
    @20
    @15
    isnumi
    sylancr
    ralrimiva
    vx
    dfac12
    sylibr
    dfac10
    sylib
    syl5eleqr
    @3
    cardid2
    @6
    @3
    engch
    3syl
    mpbid
    @5
    @2
    @13
    a1i
    2thd
    eqrdv
    impbii
end
