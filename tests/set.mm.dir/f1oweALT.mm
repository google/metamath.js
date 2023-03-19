include "wf1o.mm"
include "wfr.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "wral.mm"
include "wa.mm"
include "wwe.mm"
include "wfo.mm"
include "wi.mm"
include "f1ofo.mm"
include "wfn.mm"
include "crn.mm"
include "df-fo.mm"
include "freq2.mm"
include "biimprd.mm"
include "wfun.mm"
include "cdm.mm"
include "df-fn.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wn.mm"
include "wrex.mm"
include "wal.mm"
include "cima.mm"
include "df-fr.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "funimaex.mm"
include "wex.mm"
include "n0.mm"
include "cfv.mm"
include "funfvima2.mm"
include "ne0i.mm"
include "syl6.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "imassrn.mm"
include "jctil.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "raleq.mm"
include "rexeqbi1dv.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl7.mm"
include "syl.mm"
include "com23.mm"
include "expd.mm"
include "anabsi5.mm"
include "impd.mm"
include "cres.mm"
include "wb.mm"
include "fores.mm"
include "fvres.mm"
include "breqan12rd.mm"
include "fveq2.mm"
include "breq1d.mm"
include "breq2d.mm"
include "brab.mm"
include "syl6rbbr.mm"
include "notbid.mm"
include "ralbidva.mm"
include "rexbiia.mm"
include "breq1.mm"
include "cbvfo.mm"
include "rexbidv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "cbvexfo.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "sylibrd.mm"
include "exp4b.mm"
include "com34.mm"
include "imp4a.mm"
include "alrimdv.mm"
include "syl6ibr.mm"
include "biimpd.mm"
include "sylan9.mm"
include "sylbi.mm"
include "sylan9r.mm"
include "wf1.mm"
include "df-f1o.mm"
include "a1i.mm"
include "f1fveq.mm"
include "bicomd.mm"
include "3orbi123d.mm"
include "2ralbidva.mm"
include "eqeq1.mm"
include "eqeq2.mm"
include "sylan9bb.mm"
include "anim12d.mm"
include "dfwe2.mm"
include "3imtr4g.mm"

theorem f1oweALT
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let vw: setvar w
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  assume f1oweALT.1: |- R = { <. x , y >. | ( F ` x ) S ( F ` y ) }

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint F x
  disjoint F y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint f z
  disjoint R z
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint R w
  disjoint u v
  disjoint f v
  disjoint R v
  disjoint f u
  disjoint R u
  disjoint R f
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint S z
  disjoint S w
  disjoint S v
  disjoint S u
  disjoint S f
  disjoint A z
  disjoint A w
  disjoint A v
  disjoint A u
  disjoint A f
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint B f
  disjoint F z
  disjoint F w
  disjoint F v
  disjoint F u
  disjoint F f
  assert |- ( F : A -1-1-onto-> B -> ( S We B -> R We A ) )

  proof
    cA
    cB
    cF
    wf1o
    #
    cB
    cS
    wfr
    #
    vu
    cv
    #
    vf
    cv
    #
    cS
    wbr
    #
    @2
    @3
    wceq
    #
    @3
    @2
    cS
    wbr
    #
    w3o
    #
    vf
    cB
    wral
    #
    vu
    cB
    wral
    #
    wa
    cA
    cR
    wfr
    #
    vw
    cv
    #
    vv
    cv
    #
    cR
    wbr
    #
    @11
    @12
    wceq
    #
    @12
    @11
    cR
    wbr
    #
    w3o
    #
    vv
    cA
    wral
    vw
    cA
    wral
    #
    wa
    cB
    cS
    wwe
    cA
    cR
    wwe
    @0
    @1
    @10
    @9
    @17
    @0
    cA
    cB
    cF
    wfo
    #
    @1
    @10
    wi
    #
    cA
    cB
    cF
    f1ofo
    @18
    cF
    cA
    wfn
    #
    cF
    crn
    #
    cB
    wceq
    #
    wa
    @19
    cA
    cB
    cF
    df-fo
    @22
    @1
    @21
    cS
    wfr
    #
    @20
    @10
    @22
    @23
    @1
    @21
    cB
    cS
    freq2
    biimprd
    @20
    cF
    wfun
    #
    cF
    cdm
    #
    cA
    wceq
    #
    wa
    @23
    @10
    wi
    cF
    cA
    df-fn
    @24
    @23
    @25
    cR
    wfr
    #
    @26
    @10
    @24
    @23
    vz
    cv
    #
    @25
    wss
    #
    @28
    c0
    wne
    #
    wa
    @15
    wn
    #
    vv
    @28
    wral
    #
    vw
    @28
    wrex
    #
    wi
    #
    vz
    wal
    @27
    @24
    @23
    @34
    vz
    @24
    @23
    @29
    @30
    @33
    @24
    @29
    @23
    @30
    @33
    wi
    @24
    @29
    @30
    @23
    @33
    @24
    @29
    @30
    @23
    @33
    @24
    @29
    wa
    #
    @30
    @23
    wa
    @6
    wn
    #
    vf
    cF
    @28
    cima
    #
    wral
    #
    vu
    @37
    wrex
    #
    @33
    @35
    @30
    @23
    @39
    @24
    @29
    @30
    @23
    @39
    wi
    #
    wi
    @24
    @35
    @30
    @40
    @24
    @23
    @35
    @30
    wa
    #
    @39
    @23
    @11
    @21
    wss
    #
    @11
    c0
    wne
    #
    wa
    #
    @36
    vf
    @11
    wral
    #
    vu
    @11
    wrex
    #
    wi
    #
    vw
    wal
    #
    @24
    @41
    @39
    wi
    #
    vw
    vu
    vf
    @21
    cS
    df-fr
    @24
    @37
    cvv
    wcel
    #
    @48
    @49
    wi
    cF
    @28
    vz
    vex
    funimaex
    @41
    @37
    @21
    wss
    #
    @37
    c0
    wne
    #
    wa
    #
    @50
    @48
    @39
    @41
    @52
    @51
    @35
    @30
    @52
    @30
    @11
    @28
    wcel
    #
    vw
    wex
    @35
    @52
    vw
    @28
    n0
    @35
    @54
    @52
    vw
    @35
    @54
    @11
    cF
    cfv
    #
    @37
    wcel
    @52
    @28
    @11
    cF
    funfvima2
    @37
    @55
    ne0i
    syl6
    exlimdv
    syl5bi
    imp
    cF
    @28
    imassrn
    jctil
    @47
    @53
    @39
    wi
    vw
    @37
    cvv
    @11
    @37
    wceq
    #
    @44
    @53
    @46
    @39
    @56
    @42
    @51
    @43
    @52
    @11
    @37
    @21
    sseq1
    @11
    @37
    c0
    neeq1
    anbi12d
    @45
    @38
    vu
    @11
    @37
    @36
    vf
    @11
    @37
    raleq
    rexeqbi1dv
    imbi12d
    spcgv
    syl7
    syl
    syl5bi
    com23
    expd
    anabsi5
    impd
    @35
    @28
    @37
    cF
    @28
    cres
    #
    wfo
    #
    @33
    @39
    wb
    @28
    cF
    fores
    @33
    @12
    @57
    cfv
    #
    @11
    @57
    cfv
    #
    cS
    wbr
    #
    wn
    #
    vv
    @28
    wral
    #
    vw
    @28
    wrex
    #
    @58
    @39
    @32
    @63
    vw
    @28
    @54
    @31
    @62
    vv
    @28
    @54
    @12
    @28
    wcel
    #
    wa
    #
    @15
    @61
    @66
    @61
    @12
    cF
    cfv
    #
    @55
    cS
    wbr
    #
    @15
    @65
    @54
    @59
    @67
    @60
    @55
    cS
    @12
    @28
    cF
    fvres
    @11
    @28
    cF
    fvres
    breqan12rd
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cS
    wbr
    #
    @67
    @72
    cS
    wbr
    @68
    vx
    vy
    @12
    @11
    cR
    vv
    vex
    #
    vw
    vex
    #
    @69
    @12
    wceq
    @70
    @67
    @72
    cS
    @69
    @12
    cF
    fveq2
    breq1d
    @71
    @11
    wceq
    @72
    @55
    @67
    cS
    @71
    @11
    cF
    fveq2
    breq2d
    f1oweALT.1
    brab
    #
    syl6rbbr
    notbid
    ralbidva
    rexbiia
    @58
    @64
    @3
    @60
    cS
    wbr
    #
    wn
    #
    vf
    @37
    wral
    #
    vw
    @28
    wrex
    @39
    @58
    @63
    @79
    vw
    @28
    @62
    @78
    vv
    vf
    @28
    @37
    @57
    @59
    @3
    wceq
    @61
    @77
    @59
    @3
    @60
    cS
    breq1
    notbid
    cbvfo
    rexbidv
    @79
    @38
    vw
    vu
    @28
    @37
    @57
    @60
    @2
    wceq
    #
    @78
    @36
    vf
    @37
    @80
    @77
    @6
    @60
    @2
    @3
    cS
    breq2
    notbid
    ralbidv
    cbvexfo
    bitrd
    syl5bb
    syl
    sylibrd
    exp4b
    com34
    com23
    imp4a
    alrimdv
    vz
    vw
    vv
    @25
    cR
    df-fr
    syl6ibr
    @26
    @27
    @10
    @25
    cA
    cR
    freq2
    biimpd
    sylan9
    sylbi
    sylan9r
    sylbi
    syl
    @0
    @17
    @9
    @0
    cA
    cB
    cF
    wf1
    #
    @18
    wa
    @17
    @9
    wb
    cA
    cB
    cF
    df-f1o
    @81
    @17
    @55
    @67
    cS
    wbr
    #
    @55
    @67
    wceq
    #
    @68
    w3o
    #
    vv
    cA
    wral
    #
    vw
    cA
    wral
    #
    @18
    @9
    @81
    @16
    @84
    vw
    vv
    cA
    cA
    @81
    @11
    cA
    wcel
    @12
    cA
    wcel
    wa
    wa
    #
    @13
    @82
    @14
    @83
    @15
    @68
    @13
    @82
    wb
    @87
    @73
    @55
    @72
    cS
    wbr
    @82
    vx
    vy
    @11
    @12
    cR
    @75
    @74
    @69
    @11
    wceq
    @70
    @55
    @72
    cS
    @69
    @11
    cF
    fveq2
    breq1d
    @71
    @12
    wceq
    @72
    @67
    @55
    cS
    @71
    @12
    cF
    fveq2
    breq2d
    f1oweALT.1
    brab
    a1i
    @87
    @83
    @14
    cA
    cB
    @11
    @12
    cF
    f1fveq
    bicomd
    @15
    @68
    wb
    @87
    @76
    a1i
    3orbi123d
    2ralbidva
    @18
    @86
    @2
    @67
    cS
    wbr
    #
    @2
    @67
    wceq
    #
    @67
    @2
    cS
    wbr
    #
    w3o
    #
    vv
    cA
    wral
    #
    vu
    cB
    wral
    @9
    @85
    @92
    vw
    vu
    cA
    cB
    cF
    @55
    @2
    wceq
    #
    @84
    @91
    vv
    cA
    @93
    @82
    @88
    @83
    @89
    @68
    @90
    @55
    @2
    @67
    cS
    breq1
    @55
    @2
    @67
    eqeq1
    @55
    @2
    @67
    cS
    breq2
    3orbi123d
    ralbidv
    cbvfo
    @18
    @92
    @8
    vu
    cB
    @91
    @7
    vv
    vf
    cA
    cB
    cF
    @67
    @3
    wceq
    @88
    @4
    @89
    @5
    @90
    @6
    @67
    @3
    @2
    cS
    breq2
    @67
    @3
    @2
    eqeq2
    @67
    @3
    @2
    cS
    breq1
    3orbi123d
    cbvfo
    ralbidv
    bitrd
    sylan9bb
    sylbi
    biimprd
    anim12d
    vu
    vf
    cB
    cS
    dfwe2
    vw
    vv
    cA
    cR
    dfwe2
    3imtr4g
end
