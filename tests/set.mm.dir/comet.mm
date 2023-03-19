include "ccom.mm"
include "cxmt.mm"
include "elfvexd.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "wf.mm"
include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "wcel.mm"
include "wral.mm"
include "cfv.mm"
include "xmetf.mm"
include "syl.mm"
include "ffn.mm"
include "wa.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "xmetcl.mm"
include "xmetge0.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "3expb.mm"
include "sylan.mm"
include "ralrimivva.mm"
include "ffnov.mm"
include "fco.mm"
include "syl2anc.mm"
include "wceq.mm"
include "cop.mm"
include "opelxpi.mm"
include "fvco3.mm"
include "syl2an.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "3eqtr4g.mm"
include "eqeq1d.mm"
include "wb.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "fveq2.mm"
include "eqeq1.mm"
include "bibi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "xmeteq0.mm"
include "3bitrd.mm"
include "cxad.mm"
include "3adantr3.mm"
include "ffvelrnd.mm"
include "simpr3.mm"
include "simpr1.mm"
include "fovrnd.mm"
include "simpr2.mm"
include "ge0xaddcl.mm"
include "xaddcld.mm"
include "3anrot.mm"
include "xmettri2.mm"
include "sylan2br.mm"
include "wi.mm"
include "breq1.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "mpd.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "xrletrd.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "isxmetd.mm"

theorem comet
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cF: class F
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume comet.1: |- ( ph -> D e. ( *Met ` X ) )
  assume comet.2: |- ( ph -> F : ( 0 [,] +oo ) --> RR* )
  assume comet.3: |- ( ( ph /\ x e. ( 0 [,] +oo ) ) -> ( ( F ` x ) = 0 <-> x = 0 ) )
  assume comet.4: |- ( ( ph /\ ( x e. ( 0 [,] +oo ) /\ y e. ( 0 [,] +oo ) ) ) -> ( x <_ y -> ( F ` x ) <_ ( F ` y ) ) )
  assume comet.5: |- ( ( ph /\ ( x e. ( 0 [,] +oo ) /\ y e. ( 0 [,] +oo ) ) ) -> ( F ` ( x +e y ) ) <_ ( ( F ` x ) +e ( F ` y ) ) )

  disjoint x y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint D a
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint D b
  disjoint c x
  disjoint c y
  disjoint D c
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint X a
  disjoint X b
  disjoint X c
  assert |- ( ph -> ( F o. D ) e. ( *Met ` X ) )

  proof
    wph
    va
    vb
    vc
    cF
    cD
    ccom
    #
    cX
    wph
    cD
    cxmt
    cX
    comet.1
    elfvexd
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    cF
    wf
    #
    cX
    cX
    cxp
    #
    @1
    cD
    wf
    #
    @3
    cxr
    @0
    wf
    comet.2
    wph
    cD
    @3
    wfn
    #
    va
    cv
    #
    vb
    cv
    #
    cD
    co
    #
    @1
    wcel
    #
    vb
    cX
    wral
    va
    cX
    wral
    @4
    wph
    @3
    cxr
    cD
    wf
    #
    @5
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @10
    comet.1
    cD
    cX
    xmetf
    syl
    #
    @3
    cxr
    cD
    ffn
    syl
    wph
    @9
    va
    vb
    cX
    cX
    wph
    @11
    @6
    cX
    wcel
    #
    @7
    cX
    wcel
    #
    wa
    #
    @9
    comet.1
    @11
    @13
    @14
    @9
    @11
    @13
    @14
    w3a
    @8
    cxr
    wcel
    cc0
    @8
    cle
    wbr
    @9
    @6
    @7
    cD
    cX
    xmetcl
    @6
    @7
    cD
    cX
    xmetge0
    @8
    elxrge0
    sylanbrc
    3expb
    sylan
    #
    ralrimivva
    va
    vb
    cX
    cX
    @1
    cD
    ffnov
    sylanbrc
    #
    @3
    @1
    cxr
    cF
    cD
    fco
    syl2anc
    wph
    @15
    wa
    #
    @6
    @7
    @0
    co
    #
    cc0
    wceq
    @8
    cF
    cfv
    #
    cc0
    wceq
    #
    @8
    cc0
    wceq
    #
    @6
    @7
    wceq
    #
    @18
    @19
    @20
    cc0
    @18
    @6
    @7
    cop
    #
    @0
    cfv
    #
    @24
    cD
    cfv
    #
    cF
    cfv
    #
    @19
    @20
    wph
    @10
    @24
    @3
    wcel
    @25
    @27
    wceq
    @15
    @12
    @6
    @7
    cX
    cX
    opelxpi
    @3
    cxr
    @24
    cF
    cD
    fvco3
    syl2an
    @6
    @7
    @0
    df-ov
    @8
    @26
    cF
    @6
    @7
    cD
    df-ov
    fveq2i
    3eqtr4g
    #
    eqeq1d
    @18
    @9
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    @29
    cc0
    wceq
    #
    wb
    #
    vx
    @1
    wral
    #
    @21
    @22
    wb
    #
    @16
    wph
    @34
    @15
    wph
    @33
    vx
    @1
    comet.3
    ralrimiva
    adantr
    @33
    @35
    vx
    @8
    @1
    @29
    @8
    wceq
    #
    @31
    @21
    @32
    @22
    @36
    @30
    @20
    cc0
    @29
    @8
    cF
    fveq2
    #
    eqeq1d
    @29
    @8
    cc0
    eqeq1
    bibi12d
    rspcv
    sylc
    wph
    @11
    @15
    @22
    @23
    wb
    #
    comet.1
    @11
    @13
    @14
    @38
    @6
    @7
    cD
    cX
    xmeteq0
    3expb
    sylan
    3bitrd
    wph
    @13
    @14
    vc
    cv
    #
    cX
    wcel
    #
    w3a
    #
    wa
    #
    @20
    @39
    @6
    cD
    co
    #
    cF
    cfv
    #
    @39
    @7
    cD
    co
    #
    cF
    cfv
    #
    cxad
    co
    #
    @19
    @39
    @6
    @0
    co
    #
    @39
    @7
    @0
    co
    #
    cxad
    co
    cle
    @42
    @20
    @43
    @45
    cxad
    co
    #
    cF
    cfv
    #
    @47
    @42
    @1
    cxr
    @8
    cF
    wph
    @2
    @41
    comet.2
    adantr
    #
    wph
    @13
    @14
    @9
    @40
    @16
    3adantr3
    #
    ffvelrnd
    @42
    @1
    cxr
    @50
    cF
    @52
    @42
    @43
    @1
    wcel
    #
    @45
    @1
    wcel
    #
    @50
    @1
    wcel
    #
    @42
    @39
    @6
    @1
    cX
    cX
    cD
    wph
    @4
    @41
    @17
    adantr
    #
    wph
    @13
    @14
    @40
    simpr3
    #
    wph
    @13
    @14
    @40
    simpr1
    #
    fovrnd
    #
    @42
    @39
    @7
    @1
    cX
    cX
    cD
    @57
    @58
    wph
    @13
    @14
    @40
    simpr2
    #
    fovrnd
    #
    @43
    @45
    ge0xaddcl
    syl2anc
    #
    ffvelrnd
    @42
    @44
    @46
    @42
    @1
    cxr
    @43
    cF
    @52
    @60
    ffvelrnd
    @42
    @1
    cxr
    @45
    cF
    @52
    @62
    ffvelrnd
    xaddcld
    @42
    @8
    @50
    cle
    wbr
    #
    @20
    @51
    cle
    wbr
    #
    wph
    @11
    @41
    @64
    comet.1
    @41
    @11
    @40
    @13
    @14
    w3a
    @64
    @40
    @13
    @14
    3anrot
    @6
    @7
    @39
    cD
    cX
    xmettri2
    sylan2br
    sylan
    @42
    @9
    @56
    @29
    vy
    cv
    #
    cle
    wbr
    #
    @30
    @66
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    @64
    @65
    wi
    #
    @53
    @63
    wph
    @71
    @41
    wph
    @70
    vx
    vy
    @1
    @1
    comet.4
    ralrimivva
    adantr
    @70
    @72
    @8
    @66
    cle
    wbr
    #
    @20
    @68
    cle
    wbr
    #
    wi
    vx
    vy
    @8
    @50
    @1
    @1
    @36
    @67
    @73
    @69
    @74
    @29
    @8
    @66
    cle
    breq1
    @36
    @30
    @20
    @68
    cle
    @37
    breq1d
    imbi12d
    @66
    @50
    wceq
    #
    @73
    @64
    @74
    @65
    @66
    @50
    @8
    cle
    breq2
    @75
    @68
    @51
    @20
    cle
    @66
    @50
    cF
    fveq2
    breq2d
    imbi12d
    rspc2va
    syl21anc
    mpd
    @42
    @54
    @55
    @29
    @66
    cxad
    co
    #
    cF
    cfv
    #
    @30
    @68
    cxad
    co
    #
    cle
    wbr
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    @51
    @47
    cle
    wbr
    #
    @60
    @62
    wph
    @80
    @41
    wph
    @79
    vx
    vy
    @1
    @1
    comet.5
    ralrimivva
    adantr
    @79
    @81
    @43
    @66
    cxad
    co
    #
    cF
    cfv
    #
    @44
    @68
    cxad
    co
    #
    cle
    wbr
    vx
    vy
    @43
    @45
    @1
    @1
    @29
    @43
    wceq
    #
    @77
    @83
    @78
    @84
    cle
    @85
    @76
    @82
    cF
    @29
    @43
    @66
    cxad
    oveq1
    fveq2d
    @85
    @30
    @44
    @68
    cxad
    @29
    @43
    cF
    fveq2
    oveq1d
    breq12d
    @66
    @45
    wceq
    #
    @83
    @51
    @84
    @47
    cle
    @86
    @82
    @50
    cF
    @66
    @45
    @43
    cxad
    oveq2
    fveq2d
    @86
    @68
    @46
    @44
    cxad
    @66
    @45
    cF
    fveq2
    oveq2d
    breq12d
    rspc2va
    syl21anc
    xrletrd
    wph
    @13
    @14
    @19
    @20
    wceq
    @40
    @28
    3adantr3
    @42
    @48
    @44
    @49
    @46
    cxad
    @42
    @39
    @6
    cop
    #
    @0
    cfv
    #
    @87
    cD
    cfv
    #
    cF
    cfv
    #
    @48
    @44
    @42
    @10
    @87
    @3
    wcel
    #
    @88
    @90
    wceq
    wph
    @10
    @41
    @12
    adantr
    #
    @42
    @40
    @13
    @91
    @58
    @59
    @39
    @6
    cX
    cX
    opelxpi
    syl2anc
    @3
    cxr
    @87
    cF
    cD
    fvco3
    syl2anc
    @39
    @6
    @0
    df-ov
    @43
    @89
    cF
    @39
    @6
    cD
    df-ov
    fveq2i
    3eqtr4g
    @42
    @39
    @7
    cop
    #
    @0
    cfv
    #
    @93
    cD
    cfv
    #
    cF
    cfv
    #
    @49
    @46
    @42
    @10
    @93
    @3
    wcel
    #
    @94
    @96
    wceq
    @92
    @42
    @40
    @14
    @97
    @58
    @61
    @39
    @7
    cX
    cX
    opelxpi
    syl2anc
    @3
    cxr
    @93
    cF
    cD
    fvco3
    syl2anc
    @39
    @7
    @0
    df-ov
    @45
    @95
    cF
    @39
    @7
    cD
    df-ov
    fveq2i
    3eqtr4g
    oveq12d
    3brtr4d
    isxmetd
end
