include "cvv.mm"
include "wcel.mm"
include "c2o.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wiso.mm"
include "pw2f1o2.mm"
include "wa.mm"
include "cep.mm"
include "wceq.mm"
include "wi.mm"
include "wrex.mm"
include "wn.mm"
include "fvex.mm"
include "epelc.mm"
include "c1o.mm"
include "wf.mm"
include "elmapi.mm"
include "ad2antrl.mm"
include "ffvelrnda.mm"
include "ad2antll.mm"
include "c0.mm"
include "wo.mm"
include "n0i.mm"
include "adantl.mm"
include "cpr.mm"
include "elpri.mm"
include "df2o3.mm"
include "eleq2s.mm"
include "ad2antlr.mm"
include "orel1.mm"
include "sylc.mm"
include "1on.mm"
include "onirri.mm"
include "eleq12.mm"
include "biimpd.mm"
include "expcom.mm"
include "com3r.mm"
include "imp.mm"
include "adantll.mm"
include "mtoi.mm"
include "mpdan.mm"
include "jca.mm"
include "adantr.mm"
include "orel2.mm"
include "mpan9.mm"
include "adantrl.mm"
include "0lt1o.mm"
include "syl6eqel.mm"
include "simprl.mm"
include "eleqtrrd.mm"
include "impbida.mm"
include "syl2anc.mm"
include "simplrr.mm"
include "pw2f1o2val2.mm"
include "sylancom.mm"
include "simplrl.mm"
include "notbid.mm"
include "anbi12d.mm"
include "bitr4d.mm"
include "syl5bb.mm"
include "eqeq1.mm"
include "simplr.mm"
include "1n0.mm"
include "nesymi.mm"
include "mtbiri.mm"
include "simpr.mm"
include "mtbid.mm"
include "ad3antlr.mm"
include "eqtr4d.mm"
include "ex.mm"
include "mpbid.mm"
include "mpjaodan.mm"
include "impbid2.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "vex.mm"
include "fveq1.mm"
include "breqan12d.mm"
include "eqeqan12d.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "braba.mm"
include "wel.mm"
include "eleq2.mm"
include "bi2anan9r.mm"
include "bi2bian9.mm"
include "3bitr4g.mm"
include "ralrimivva.mm"
include "df-isom.mm"
include "sylanbrc.mm"

theorem wepwsolem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cR: class R
  let cT: class T
  let cU: class U
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume wepwso.t: |- T = { <. x , y >. | E. z e. A ( ( z e. y /\ -. z e. x ) /\ A. w e. A ( w R z -> ( w e. x <-> w e. y ) ) ) }
  assume wepwso.u: |- U = { <. x , y >. | E. z e. A ( ( x ` z ) _E ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }
  assume wepwso.f: |- F = ( a e. ( 2o ^m A ) |-> ( `' a " { 1o } ) )

  disjoint R x
  disjoint R y
  disjoint R z
  disjoint R w
  disjoint R a
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint a x
  disjoint y z
  disjoint w y
  disjoint a y
  disjoint w z
  disjoint a z
  disjoint a w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint A w
  disjoint A a
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint F w
  disjoint T a
  disjoint U a
  disjoint R b
  disjoint R c
  disjoint b x
  disjoint c x
  disjoint b y
  disjoint c y
  disjoint b z
  disjoint c z
  disjoint b w
  disjoint c w
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint A b
  disjoint A c
  disjoint F b
  disjoint F c
  disjoint T b
  disjoint T c
  disjoint U b
  disjoint U c
  assert |- ( A e. _V -> F Isom U , T ( ( 2o ^m A ) , ~P A ) )

  proof
    cA
    cvv
    wcel
    #
    c2o
    cA
    cmap
    co
    #
    cA
    cpw
    #
    cF
    wf1o
    vb
    cv
    #
    vc
    cv
    #
    cU
    wbr
    #
    @3
    cF
    cfv
    #
    @4
    cF
    cfv
    #
    cT
    wbr
    #
    wb
    #
    vc
    @1
    wral
    vb
    @1
    wral
    @1
    @2
    cU
    cT
    cF
    wiso
    va
    cA
    cF
    cvv
    wepwso.f
    pw2f1o2
    @0
    @9
    vb
    vc
    @1
    @1
    @0
    @3
    @1
    wcel
    #
    @4
    @1
    wcel
    #
    wa
    wa
    #
    vz
    cv
    #
    @3
    cfv
    #
    @13
    @4
    cfv
    #
    cep
    wbr
    #
    vw
    cv
    #
    @13
    cR
    wbr
    #
    @17
    @3
    cfv
    #
    @17
    @4
    cfv
    #
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    wa
    #
    vz
    cA
    wrex
    #
    @13
    @7
    wcel
    #
    @13
    @6
    wcel
    #
    wn
    #
    wa
    #
    @18
    @17
    @6
    wcel
    #
    @17
    @7
    wcel
    #
    wb
    #
    wi
    #
    vw
    cA
    wral
    #
    wa
    #
    vz
    cA
    wrex
    #
    @5
    @8
    @12
    @24
    @35
    vz
    cA
    @12
    @13
    cA
    wcel
    #
    wa
    #
    @16
    @29
    @23
    @34
    @16
    @14
    @15
    wcel
    #
    @38
    @29
    @14
    @15
    @13
    @4
    fvex
    epelc
    @38
    @39
    @15
    c1o
    wceq
    #
    @14
    c1o
    wceq
    #
    wn
    #
    wa
    #
    @29
    @38
    @14
    c2o
    wcel
    #
    @15
    c2o
    wcel
    #
    @39
    @43
    wb
    @12
    cA
    c2o
    @13
    @3
    @10
    cA
    c2o
    @3
    wf
    @0
    @11
    @3
    c2o
    cA
    elmapi
    ad2antrl
    #
    ffvelrnda
    @12
    cA
    c2o
    @13
    @4
    @11
    cA
    c2o
    @4
    wf
    @0
    @10
    @4
    c2o
    cA
    elmapi
    ad2antll
    #
    ffvelrnda
    @44
    @45
    wa
    #
    @39
    @43
    @48
    @39
    wa
    #
    @40
    @42
    @49
    @15
    c0
    wceq
    #
    wn
    #
    @50
    @40
    wo
    #
    @40
    @39
    @51
    @48
    @15
    @14
    n0i
    adantl
    @45
    @52
    @44
    @39
    @52
    @15
    c0
    c1o
    cpr
    #
    c2o
    @15
    c0
    c1o
    elpri
    df2o3
    eleq2s
    ad2antlr
    @50
    @40
    orel1
    sylc
    #
    @49
    @40
    @42
    @54
    @49
    @40
    wa
    @41
    c1o
    c1o
    wcel
    #
    c1o
    1on
    onirri
    @39
    @40
    @41
    @55
    wi
    #
    @48
    @39
    @40
    @56
    @40
    @41
    @39
    @55
    @41
    @40
    @39
    @55
    wi
    @41
    @40
    wa
    @39
    @55
    @14
    c1o
    @15
    c1o
    eleq12
    biimpd
    expcom
    com3r
    imp
    adantll
    mtoi
    mpdan
    jca
    @48
    @43
    wa
    #
    @14
    c1o
    @15
    @57
    @14
    c0
    c1o
    @48
    @42
    @14
    c0
    wceq
    #
    @40
    @48
    @58
    @41
    wo
    #
    @42
    @58
    @44
    @59
    @45
    @59
    @14
    @53
    c2o
    @14
    c0
    c1o
    elpri
    df2o3
    eleq2s
    adantr
    @41
    @58
    orel2
    mpan9
    adantrl
    0lt1o
    syl6eqel
    @48
    @40
    @42
    simprl
    eleqtrrd
    impbida
    syl2anc
    @38
    @26
    @40
    @28
    @42
    @12
    @37
    @11
    @26
    @40
    wb
    @0
    @10
    @11
    @37
    simplrr
    va
    cA
    cF
    @4
    @13
    wepwso.f
    pw2f1o2val2
    sylancom
    @38
    @27
    @41
    @12
    @37
    @10
    @27
    @41
    wb
    @0
    @10
    @11
    @37
    simplrl
    va
    cA
    cF
    @3
    @13
    wepwso.f
    pw2f1o2val2
    sylancom
    notbid
    anbi12d
    bitr4d
    syl5bb
    @12
    @23
    @34
    wb
    @37
    @12
    @22
    @33
    vw
    cA
    @12
    @17
    cA
    wcel
    #
    wa
    #
    @21
    @32
    @18
    @61
    @21
    @19
    c1o
    wceq
    #
    @20
    c1o
    wceq
    #
    wb
    #
    @32
    @61
    @19
    c2o
    wcel
    #
    @20
    c2o
    wcel
    #
    @21
    @64
    wb
    @12
    cA
    c2o
    @17
    @3
    @46
    ffvelrnda
    @12
    cA
    c2o
    @17
    @4
    @47
    ffvelrnda
    @65
    @66
    wa
    #
    @21
    @64
    @19
    @20
    c1o
    eqeq1
    @67
    @19
    c0
    wceq
    #
    @64
    @21
    wi
    @62
    @67
    @68
    wa
    #
    @64
    @21
    @69
    @64
    wa
    #
    @19
    c0
    @20
    @67
    @68
    @64
    simplr
    @70
    @63
    wn
    @20
    c0
    wceq
    #
    @63
    wo
    #
    @71
    @70
    @62
    @63
    @68
    @62
    wn
    @67
    @64
    @68
    @62
    c0
    c1o
    wceq
    c1o
    c0
    1n0
    nesymi
    @19
    c0
    c1o
    eqeq1
    mtbiri
    ad2antlr
    @69
    @64
    simpr
    mtbid
    @66
    @72
    @65
    @68
    @64
    @72
    @20
    @53
    c2o
    @20
    c0
    c1o
    elpri
    df2o3
    eleq2s
    ad3antlr
    @63
    @71
    orel2
    sylc
    eqtr4d
    ex
    @67
    @62
    wa
    #
    @64
    @21
    @73
    @64
    wa
    #
    @19
    c1o
    @20
    @67
    @62
    @64
    simplr
    #
    @74
    @62
    @63
    @75
    @73
    @64
    simpr
    mpbid
    eqtr4d
    ex
    @65
    @68
    @62
    wo
    #
    @66
    @76
    @19
    @53
    c2o
    @19
    c0
    c1o
    elpri
    df2o3
    eleq2s
    adantr
    mpjaodan
    impbid2
    syl2anc
    @61
    @30
    @62
    @31
    @63
    @12
    @60
    @10
    @30
    @62
    wb
    @0
    @10
    @11
    @60
    simplrl
    va
    cA
    cF
    @3
    @17
    wepwso.f
    pw2f1o2val2
    sylancom
    @12
    @60
    @11
    @31
    @63
    wb
    @0
    @10
    @11
    @60
    simplrr
    va
    cA
    cF
    @4
    @17
    wepwso.f
    pw2f1o2val2
    sylancom
    bibi12d
    bitr4d
    imbi2d
    ralbidva
    adantr
    anbi12d
    rexbidva
    @13
    vx
    cv
    #
    cfv
    #
    @13
    vy
    cv
    #
    cfv
    #
    cep
    wbr
    #
    @18
    @17
    @77
    cfv
    #
    @17
    @79
    cfv
    #
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    wa
    #
    vz
    cA
    wrex
    @25
    vx
    vy
    @3
    @4
    cU
    vb
    vex
    vc
    vex
    @77
    @3
    wceq
    #
    @79
    @4
    wceq
    #
    wa
    #
    @87
    @24
    vz
    cA
    @90
    @81
    @16
    @86
    @23
    @88
    @89
    @78
    @14
    @80
    @15
    cep
    @13
    @77
    @3
    fveq1
    @13
    @79
    @4
    fveq1
    breqan12d
    @90
    @85
    @22
    vw
    cA
    @90
    @84
    @21
    @18
    @88
    @89
    @82
    @19
    @83
    @20
    @17
    @77
    @3
    fveq1
    @17
    @79
    @4
    fveq1
    eqeqan12d
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    wepwso.u
    braba
    vz
    vy
    wel
    #
    vz
    vx
    wel
    #
    wn
    #
    wa
    #
    @18
    vw
    vx
    wel
    #
    vw
    vy
    wel
    #
    wb
    #
    wi
    #
    vw
    cA
    wral
    #
    wa
    #
    vz
    cA
    wrex
    @36
    vx
    vy
    @6
    @7
    cT
    @3
    cF
    fvex
    @4
    cF
    fvex
    @77
    @6
    wceq
    #
    @79
    @7
    wceq
    #
    wa
    #
    @100
    @35
    vz
    cA
    @103
    @94
    @29
    @99
    @34
    @102
    @91
    @26
    @101
    @93
    @28
    @79
    @7
    @13
    eleq2
    @101
    @92
    @27
    @77
    @6
    @13
    eleq2
    notbid
    bi2anan9r
    @103
    @98
    @33
    vw
    cA
    @103
    @97
    @32
    @18
    @101
    @95
    @30
    @102
    @96
    @31
    @77
    @6
    @17
    eleq2
    @79
    @7
    @17
    eleq2
    bi2bian9
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    wepwso.t
    braba
    3bitr4g
    ralrimivva
    vb
    vc
    @1
    @2
    cU
    cT
    cF
    df-isom
    sylanbrc
end
