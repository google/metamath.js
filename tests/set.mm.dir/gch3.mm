include "cgch.mm"
include "cvv.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "cale.mm"
include "cfv.mm"
include "cpw.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "fvex.mm"
include "simpl.mm"
include "syl5eleqr.mm"
include "gchaleph2.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "alephgch.mm"
include "ralimi.mm"
include "wfn.mm"
include "alephfnon.mm"
include "ffnfv.mm"
include "mpbiran.mm"
include "sylibr.mm"
include "df-f.mm"
include "sylib.mm"
include "gch2.mm"
include "impbii.mm"

theorem gch3
  let vx: setvar x


  assert |- ( GCH = _V <-> A. x e. On ( aleph ` suc x ) ~~ ~P ( aleph ` x ) )

  proof
    cgch
    cvv
    wceq
    #
    vx
    cv
    #
    csuc
    #
    cale
    cfv
    #
    @1
    cale
    cfv
    #
    cpw
    cen
    wbr
    #
    vx
    con0
    wral
    #
    @0
    @5
    vx
    con0
    @0
    @1
    con0
    wcel
    #
    wa
    #
    @7
    @4
    cgch
    wcel
    #
    @3
    cgch
    wcel
    @5
    @0
    @7
    simpr
    @8
    @4
    cvv
    cgch
    @1
    cale
    fvex
    @0
    @7
    simpl
    #
    syl5eleqr
    @8
    @3
    cvv
    cgch
    @2
    cale
    fvex
    @10
    syl5eleqr
    @1
    gchaleph2
    syl3anc
    ralrimiva
    @6
    cale
    crn
    cgch
    wss
    #
    @0
    @6
    con0
    cgch
    cale
    wf
    #
    @11
    @6
    @9
    vx
    con0
    wral
    #
    @12
    @5
    @9
    vx
    con0
    @1
    alephgch
    ralimi
    @12
    cale
    con0
    wfn
    #
    @13
    alephfnon
    vx
    con0
    cgch
    cale
    ffnfv
    mpbiran
    sylibr
    @12
    @14
    @11
    alephfnon
    con0
    cgch
    cale
    df-f
    mpbiran
    sylib
    gch2
    sylibr
    impbii
end
