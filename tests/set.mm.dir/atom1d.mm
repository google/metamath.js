include "cat.mm"
include "wcel.mm"
include "cv.mm"
include "c0v.mm"
include "wne.mm"
include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "chil.mm"
include "wrex.mm"
include "cspn.mm"
include "cch.mm"
include "c0h.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "elat2.mm"
include "chne0.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfim.mm"
include "chel.mm"
include "adantrr.mm"
include "simprlr.mm"
include "h1dn0.mm"
include "sylan.mm"
include "anasss.mm"
include "wn.mm"
include "ch1dle.mm"
include "snssi.mm"
include "occl.mm"
include "3syl.mm"
include "choccl.mm"
include "sseq1.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "mpid.mm"
include "impr.mm"
include "adantrlr.mm"
include "ord.mm"
include "nne.mm"
include "syl6ibr.mm"
include "mt4d.mm"
include "eqcomd.mm"
include "rspe.mm"
include "syl12anc.mm"
include "exp44.mm"
include "rexlimd.mm"
include "sylbid.mm"
include "imp32.mm"
include "sylbi.mm"
include "h1da.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "expdcom.mm"
include "impd.mm"
include "rexlimiv.mm"
include "impbii.mm"
include "spansn.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbiia.mm"
include "bitr4i.mm"

theorem atom1d
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A e. HAtoms <-> E. x e. ~H ( x =/= 0h /\ A = ( span ` { x } ) ) )

  proof
    cA
    cat
    wcel
    #
    vx
    cv
    #
    c0v
    wne
    #
    cA
    @1
    csn
    #
    cort
    cfv
    #
    cort
    cfv
    #
    wceq
    #
    wa
    #
    vx
    chil
    wrex
    #
    @2
    cA
    @3
    cspn
    cfv
    #
    wceq
    #
    wa
    #
    vx
    chil
    wrex
    @0
    @8
    @0
    cA
    cch
    wcel
    #
    cA
    c0h
    wne
    #
    vy
    cv
    #
    cA
    wss
    #
    @14
    cA
    wceq
    #
    @14
    c0h
    wceq
    #
    wo
    #
    wi
    #
    vy
    cch
    wral
    #
    wa
    wa
    @8
    vy
    cA
    elat2
    @12
    @13
    @20
    @8
    @12
    @13
    @2
    vx
    cA
    wrex
    @20
    @8
    wi
    #
    vx
    cA
    chne0
    @12
    @2
    @21
    vx
    cA
    @12
    vx
    nfv
    @20
    @8
    vx
    @20
    vx
    nfv
    @7
    vx
    chil
    nfre1
    nfim
    @12
    @1
    cA
    wcel
    #
    @2
    @20
    @8
    @12
    @22
    @2
    wa
    #
    @20
    wa
    wa
    #
    @1
    chil
    wcel
    #
    @2
    @6
    @8
    @12
    @23
    @25
    @20
    @12
    @22
    @25
    @2
    @1
    cA
    chel
    #
    adantrr
    adantrr
    @12
    @22
    @2
    @20
    simprlr
    @24
    @5
    cA
    @24
    @5
    c0h
    wne
    #
    @5
    cA
    wceq
    #
    @12
    @23
    @27
    @20
    @12
    @22
    @2
    @27
    @12
    @22
    wa
    #
    @25
    @2
    @27
    @26
    @1
    h1dn0
    sylan
    anasss
    adantrr
    @24
    @28
    wn
    @5
    c0h
    wceq
    #
    @27
    wn
    @24
    @28
    @30
    @12
    @22
    @20
    @28
    @30
    wo
    #
    @2
    @12
    @22
    @20
    @31
    @29
    @20
    @5
    cA
    wss
    #
    @31
    cA
    @1
    ch1dle
    @29
    @4
    cch
    wcel
    #
    @5
    cch
    wcel
    @20
    @32
    @31
    wi
    #
    wi
    @29
    @25
    @3
    chil
    wss
    @33
    @26
    @1
    chil
    snssi
    @3
    occl
    3syl
    @4
    choccl
    @19
    @34
    vy
    @5
    cch
    @14
    @5
    wceq
    #
    @15
    @32
    @18
    @31
    @14
    @5
    cA
    sseq1
    @35
    @16
    @28
    @17
    @30
    @14
    @5
    cA
    eqeq1
    @14
    @5
    c0h
    eqeq1
    orbi12d
    imbi12d
    rspcv
    3syl
    mpid
    impr
    adantrlr
    ord
    @5
    c0h
    nne
    syl6ibr
    mt4d
    eqcomd
    @7
    vx
    chil
    rspe
    syl12anc
    exp44
    rexlimd
    sylbid
    imp32
    sylbi
    @7
    @0
    vx
    chil
    @25
    @2
    @6
    @0
    @6
    @25
    @2
    @0
    @25
    @2
    wa
    @0
    @6
    @5
    cat
    wcel
    @1
    h1da
    cA
    @5
    cat
    eleq1
    syl5ibr
    expdcom
    impd
    rexlimiv
    impbii
    @11
    @7
    vx
    chil
    @25
    @10
    @6
    @2
    @25
    @9
    @5
    cA
    @1
    spansn
    eqeq2d
    anbi2d
    rexbiia
    bitr4i
end
