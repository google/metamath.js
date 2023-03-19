include "cun.mm"
include "crnk.mm"
include "cfv.mm"
include "csuc.mm"
include "wceq.mm"
include "cxp.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cuni.mm"
include "rankuni.mm"
include "unieqi.mm"
include "eqtri.mm"
include "unixp.mm"
include "fveq2d.mm"
include "syl5reqr.mm"
include "suc11reg.mm"
include "sylibr.mm"
include "adantl.mm"
include "cv.mm"
include "con0.mm"
include "wrex.mm"
include "wlim.mm"
include "wn.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbii.mm"
include "sucexb.mm"
include "nlimsucg.mm"
include "syl.mm"
include "limeq.mm"
include "mtbird.mm"
include "rankxplim2.mm"
include "nsyl.mm"
include "wo.mm"
include "xpex.mm"
include "rankeq0.mm"
include "necon3abii.mm"
include "w3o.mm"
include "word.mm"
include "rankon.mm"
include "onordi.mm"
include "ordzsl.mm"
include "mpbi.mm"
include "3orass.mm"
include "ori.mm"
include "sylbi.mm"
include "ord.mm"
include "con1d.mm"
include "syl5com.mm"
include "vex.mm"
include "ax-mp.mm"
include "mtbiri.mm"
include "rexlimivw.mm"
include "rankxplim3.mm"
include "sylnib.mm"
include "syl6com.mm"
include "unixp0.mm"
include "uniex.mm"
include "eqeq1i.mm"
include "3bitri.mm"
include "onuni.mm"
include "syld.mm"
include "impcom.mm"
include "onsucuni2.mm"
include "mpan.mm"
include "eqtrd.mm"
include "imp.mm"
include "eqtr2d.mm"

theorem rankxpsuc
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume rankxplim.1: |- A e. _V
  assume rankxplim.2: |- B e. _V


  assert |- ( ( ( rank ` ( A u. B ) ) = suc C /\ ( A X. B ) =/= (/) ) -> ( rank ` ( A X. B ) ) = suc suc ( rank ` ( A u. B ) ) )

  proof
    cA
    cB
    cun
    #
    crnk
    cfv
    #
    cC
    csuc
    #
    wceq
    #
    cA
    cB
    cxp
    #
    c0
    wne
    #
    wa
    #
    @1
    csuc
    #
    csuc
    #
    @4
    crnk
    cfv
    #
    cuni
    #
    csuc
    #
    @9
    @6
    @7
    @10
    wceq
    @8
    @11
    wceq
    @6
    @7
    @10
    cuni
    #
    csuc
    #
    @10
    @5
    @7
    @13
    wceq
    #
    @3
    @5
    @1
    @12
    wceq
    @14
    @5
    @12
    @4
    cuni
    #
    cuni
    #
    crnk
    cfv
    #
    @1
    @17
    @15
    crnk
    cfv
    #
    cuni
    @12
    @15
    rankuni
    @18
    @10
    @4
    rankuni
    #
    unieqi
    eqtri
    @5
    @16
    @0
    crnk
    cA
    cB
    unixp
    fveq2d
    syl5reqr
    @1
    @12
    suc11reg
    sylibr
    adantl
    @6
    @10
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    @13
    @10
    wceq
    #
    @5
    @3
    @23
    @5
    @3
    @10
    wlim
    #
    wn
    #
    @23
    @3
    @5
    @9
    @21
    wceq
    #
    vx
    con0
    wrex
    #
    @26
    @3
    @9
    wlim
    #
    wn
    #
    @5
    @28
    @3
    @1
    wlim
    #
    @29
    @3
    @31
    @2
    wlim
    #
    @3
    cC
    cvv
    wcel
    #
    @32
    wn
    @3
    @2
    cvv
    wcel
    #
    @33
    @3
    @1
    cvv
    wcel
    @34
    @0
    crnk
    fvex
    @1
    @2
    cvv
    eleq1
    mpbii
    cC
    sucexb
    sylibr
    cC
    cvv
    nlimsucg
    syl
    @1
    @2
    limeq
    mtbird
    cA
    cB
    rankxplim.1
    rankxplim.2
    rankxplim2
    nsyl
    @5
    @28
    @29
    @5
    @28
    @29
    @5
    @9
    c0
    wceq
    #
    wn
    @28
    @29
    wo
    #
    @35
    @4
    c0
    @4
    cA
    cB
    rankxplim.1
    rankxplim.2
    xpex
    #
    rankeq0
    necon3abii
    @35
    @36
    @35
    @28
    @29
    w3o
    #
    @35
    @36
    wo
    @9
    word
    @38
    @9
    @4
    rankon
    #
    onordi
    vx
    @9
    ordzsl
    mpbi
    @35
    @28
    @29
    3orass
    mpbi
    ori
    sylbi
    ord
    con1d
    syl5com
    #
    @28
    @29
    @25
    @27
    @30
    vx
    con0
    @27
    @29
    @21
    wlim
    #
    @20
    cvv
    wcel
    @41
    wn
    vx
    vex
    @20
    cvv
    nlimsucg
    ax-mp
    @9
    @21
    limeq
    mtbiri
    rexlimivw
    cA
    cB
    rankxplim.1
    rankxplim.2
    rankxplim3
    sylnib
    syl6com
    @5
    @23
    @25
    @5
    @23
    @25
    @5
    @10
    c0
    wceq
    #
    wn
    @23
    @25
    wo
    #
    @42
    @4
    c0
    @4
    c0
    wceq
    @15
    c0
    wceq
    @18
    c0
    wceq
    @42
    cA
    cB
    unixp0
    @15
    @4
    @37
    uniex
    rankeq0
    @18
    @10
    c0
    @19
    eqeq1i
    3bitri
    necon3abii
    @42
    @43
    @42
    @23
    @25
    w3o
    #
    @42
    @43
    wo
    @10
    word
    @44
    @10
    @9
    con0
    wcel
    #
    @10
    con0
    wcel
    #
    @39
    @9
    onuni
    ax-mp
    #
    onordi
    vx
    @10
    ordzsl
    mpbi
    @42
    @23
    @25
    3orass
    mpbi
    ori
    sylbi
    ord
    con1d
    syld
    impcom
    @22
    @24
    vx
    con0
    @46
    @22
    @24
    @47
    @10
    @20
    onsucuni2
    mpan
    rexlimivw
    syl
    eqtrd
    @7
    @10
    suc11reg
    sylibr
    @6
    @28
    @11
    @9
    wceq
    #
    @3
    @5
    @28
    @40
    imp
    @27
    @48
    vx
    con0
    @45
    @27
    @48
    @39
    @9
    @20
    onsucuni2
    mpan
    rexlimivw
    syl
    eqtr2d
end
