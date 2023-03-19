include "csur.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cdm.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "wss.mm"
include "nodmon.mm"
include "c0.mm"
include "nosgnn0i.mm"
include "a1i.mm"
include "wn.mm"
include "wceq.mm"
include "word.mm"
include "nodmord.mm"
include "ordirr.mm"
include "syl.mm"
include "ndmfv.mm"
include "wfn.mm"
include "cin.mm"
include "wfun.mm"
include "nofun.mm"
include "funfn.mm"
include "sylib.mm"
include "c1o.mm"
include "c2o.mm"
include "cpr.mm"
include "fnsng.mm"
include "sylancl.mm"
include "disjsn.mm"
include "sylibr.mm"
include "snidg.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "fvsng.mm"
include "eqtrd.mm"
include "3netr4d.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "onintss.mm"
include "sylc.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "eloni.mm"
include "wo.mm"
include "ordtri2.mm"
include "eqcom.mm"
include "orbi1i.mm"
include "orcom.mm"
include "bitri.mm"
include "notbii.mm"
include "syl6bb.mm"
include "ordsseleq.mm"
include "notbid.mm"
include "ancoms.mm"
include "bitr4d.mm"
include "syl2anr.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "fvun1.mm"
include "eqcomd.mm"
include "3expia.mm"
include "sylbird.mm"
include "necon1ad.mm"
include "ralrimiva.mm"
include "weq.mm"
include "ralrab.mm"
include "ssint.mm"
include "eqssd.mm"

theorem noextenddif
  let vx: setvar x
  let cA: class A
  let cX: class X
  let vy: setvar y
  assume noextend.1: |- X e. { 1o , 2o }

  disjoint A x
  disjoint X x
  disjoint A y
  disjoint x y
  disjoint X y
  assert |- ( A e. No -> |^| { x e. On | ( A ` x ) =/= ( ( A u. { <. dom A , X >. } ) ` x ) } = dom A )

  proof
    cA
    csur
    wcel
    #
    vx
    cv
    #
    cA
    cfv
    #
    @1
    cA
    cA
    cdm
    #
    cX
    cop
    csn
    #
    cun
    #
    cfv
    #
    wne
    #
    vx
    con0
    crab
    #
    cint
    #
    @3
    @0
    @3
    con0
    wcel
    #
    @3
    cA
    cfv
    #
    @3
    @5
    cfv
    #
    wne
    #
    @9
    @3
    wss
    cA
    nodmon
    #
    @0
    c0
    cX
    @11
    @12
    c0
    cX
    wne
    @0
    cX
    noextend.1
    nosgnn0i
    a1i
    @0
    @3
    @3
    wcel
    wn
    #
    @11
    c0
    wceq
    @0
    @3
    word
    #
    @15
    cA
    nodmord
    #
    @3
    ordirr
    syl
    #
    @3
    cA
    ndmfv
    syl
    @0
    @12
    @3
    @4
    cfv
    #
    cX
    @0
    cA
    @3
    wfn
    #
    @4
    @3
    csn
    #
    wfn
    #
    @3
    @21
    cin
    c0
    wceq
    #
    @3
    @21
    wcel
    #
    @12
    @19
    wceq
    @0
    cA
    wfun
    @20
    cA
    nofun
    cA
    funfn
    sylib
    #
    @0
    @10
    cX
    c1o
    c2o
    cpr
    #
    wcel
    #
    @22
    @14
    noextend.1
    @3
    cX
    con0
    @26
    fnsng
    sylancl
    #
    @0
    @15
    @23
    @18
    @3
    @3
    disjsn
    sylibr
    #
    @0
    @10
    @24
    @14
    @3
    con0
    snidg
    syl
    @3
    @21
    cA
    @4
    @3
    fvun2
    syl112anc
    @0
    @10
    @27
    @19
    cX
    wceq
    @14
    noextend.1
    @3
    cX
    con0
    @26
    fvsng
    sylancl
    eqtrd
    3netr4d
    @7
    @13
    vx
    @3
    @1
    @3
    wceq
    @2
    @11
    @6
    @12
    @1
    @3
    cA
    fveq2
    @1
    @3
    @5
    fveq2
    neeq12d
    onintss
    sylc
    @0
    @3
    vy
    cv
    #
    wss
    #
    vy
    @8
    wral
    #
    @3
    @9
    wss
    @0
    @30
    cA
    cfv
    #
    @30
    @5
    cfv
    #
    wne
    #
    @31
    wi
    #
    vy
    con0
    wral
    @32
    @0
    @36
    vy
    con0
    @0
    @30
    con0
    wcel
    #
    wa
    #
    @31
    @33
    @34
    @38
    @31
    wn
    #
    @30
    @3
    wcel
    #
    @33
    @34
    wceq
    #
    @37
    @30
    word
    #
    @16
    @40
    @39
    wb
    @0
    @30
    eloni
    @17
    @42
    @16
    wa
    #
    @40
    @3
    @30
    wcel
    #
    @3
    @30
    wceq
    #
    wo
    #
    wn
    #
    @39
    @43
    @40
    @30
    @3
    wceq
    #
    @44
    wo
    #
    wn
    @47
    @30
    @3
    ordtri2
    @49
    @46
    @49
    @45
    @44
    wo
    @46
    @48
    @45
    @44
    @30
    @3
    eqcom
    orbi1i
    @45
    @44
    orcom
    bitri
    notbii
    syl6bb
    @16
    @42
    @39
    @47
    wb
    @16
    @42
    wa
    @31
    @46
    @3
    @30
    ordsseleq
    notbid
    ancoms
    bitr4d
    syl2anr
    @0
    @37
    @40
    @41
    @0
    @37
    @40
    w3a
    #
    @34
    @33
    @50
    @20
    @22
    @23
    @40
    @34
    @33
    wceq
    @0
    @37
    @20
    @40
    @25
    3ad2ant1
    @0
    @37
    @22
    @40
    @28
    3ad2ant1
    @0
    @37
    @23
    @40
    @29
    3ad2ant1
    @0
    @37
    @40
    simp3
    @3
    @21
    cA
    @4
    @30
    fvun1
    syl112anc
    eqcomd
    3expia
    sylbird
    necon1ad
    ralrimiva
    @7
    @35
    @31
    vy
    vx
    con0
    vx
    vy
    weq
    @2
    @33
    @6
    @34
    @1
    @30
    cA
    fveq2
    @1
    @30
    @5
    fveq2
    neeq12d
    ralrab
    sylibr
    vy
    @3
    @8
    ssint
    sylibr
    eqssd
end
