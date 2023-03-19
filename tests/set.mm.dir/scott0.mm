include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "crnk.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "crab.mm"
include "rabeq.mm"
include "rab0.mm"
include "syl6eq.mm"
include "wne.mm"
include "wrex.mm"
include "cab.mm"
include "ciin.mm"
include "wcel.mm"
include "wex.mm"
include "n0.mm"
include "nfre1.mm"
include "eqid.mm"
include "rspe.mm"
include "mpan2.mm"
include "exlimi.mm"
include "sylbi.mm"
include "wa.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "spcev.mm"
include "eximi.mm"
include "excom.mm"
include "sylibr.mm"
include "df-rex.mm"
include "exbii.mm"
include "3imtr4i.mm"
include "syl.mm"
include "abn0.mm"
include "cint.mm"
include "dfiin2.mm"
include "con0.mm"
include "rankon.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "abssi.mm"
include "onint.mm"
include "mpan.mm"
include "syl5eqel.mm"
include "nfii1.mm"
include "nfeq2.mm"
include "rexbid.mm"
include "elabg.mm"
include "ibi.mm"
include "ssid.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "iinss.mm"
include "sseq1.mm"
include "syl5ib.mm"
include "ralrimiv.mm"
include "reximi.mm"
include "4syl.mm"
include "rabn0.mm"
include "necon4i.mm"
include "impbii.mm"

theorem scott0
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A = (/) <-> { x e. A | A. y e. A ( rank ` x ) C_ ( rank ` y ) } = (/) )

  proof
    cA
    c0
    wceq
    #
    vx
    cv
    #
    crnk
    cfv
    #
    vy
    cv
    #
    crnk
    cfv
    #
    wss
    #
    vy
    cA
    wral
    #
    vx
    cA
    crab
    #
    c0
    wceq
    @0
    @7
    @6
    vx
    c0
    crab
    c0
    @6
    vx
    cA
    c0
    rabeq
    @6
    vx
    rab0
    syl6eq
    cA
    c0
    @7
    c0
    cA
    c0
    wne
    #
    @6
    vx
    cA
    wrex
    #
    @7
    c0
    wne
    @8
    @3
    @2
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    c0
    wne
    #
    vx
    cA
    @2
    ciin
    #
    @12
    wcel
    #
    @14
    @2
    wceq
    #
    vx
    cA
    wrex
    #
    @9
    @8
    @11
    vy
    wex
    #
    @13
    @8
    @2
    @2
    wceq
    #
    vx
    cA
    wrex
    #
    @18
    @8
    @1
    cA
    wcel
    #
    vx
    wex
    @20
    vx
    cA
    n0
    @21
    @20
    vx
    @19
    vx
    cA
    nfre1
    @21
    @19
    @20
    @2
    eqid
    @19
    vx
    cA
    rspe
    mpan2
    exlimi
    sylbi
    @21
    @19
    wa
    #
    vx
    wex
    #
    @21
    @10
    wa
    #
    vx
    wex
    #
    vy
    wex
    #
    @20
    @18
    @23
    @24
    vy
    wex
    #
    vx
    wex
    @26
    @22
    @27
    vx
    @24
    @22
    vy
    @2
    @1
    crnk
    fvex
    #
    @10
    @10
    @19
    @21
    @3
    @2
    @2
    eqeq1
    anbi2d
    spcev
    eximi
    @24
    vy
    vx
    excom
    sylibr
    @19
    vx
    cA
    df-rex
    @11
    @25
    vy
    @10
    vx
    cA
    df-rex
    exbii
    3imtr4i
    syl
    @11
    vy
    abn0
    sylibr
    @13
    @14
    @12
    cint
    #
    @12
    vx
    vy
    cA
    @2
    @28
    dfiin2
    @12
    con0
    wss
    @13
    @29
    @12
    wcel
    @11
    vy
    con0
    @10
    @3
    con0
    wcel
    #
    vx
    cA
    @10
    @30
    @2
    con0
    wcel
    @1
    rankon
    @3
    @2
    con0
    eleq1
    mpbiri
    rexlimivw
    abssi
    @12
    onint
    mpan
    syl5eqel
    @15
    @17
    @11
    @17
    vy
    @14
    @12
    @3
    @14
    wceq
    @10
    @16
    vx
    cA
    vx
    @3
    @14
    vx
    cA
    @2
    nfii1
    nfeq2
    @3
    @14
    @2
    eqeq1
    rexbid
    elabg
    ibi
    @16
    @6
    vx
    cA
    @16
    @5
    vy
    cA
    @3
    cA
    wcel
    #
    @14
    @4
    wss
    #
    @16
    @5
    @31
    @5
    vx
    cA
    wrex
    #
    @32
    @31
    @4
    @4
    wss
    #
    @33
    @4
    ssid
    @5
    @34
    vx
    @3
    cA
    @1
    @3
    wceq
    @2
    @4
    @4
    @1
    @3
    crnk
    fveq2
    sseq1d
    rspcev
    mpan2
    vx
    cA
    @2
    @4
    iinss
    syl
    @14
    @2
    @4
    sseq1
    syl5ib
    ralrimiv
    reximi
    4syl
    @6
    vx
    cA
    rabn0
    sylibr
    necon4i
    impbii
end
