include "cv.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "cicc.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "clt.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "0re.mm"
include "ne0ii.mm"
include "ral0.mm"
include "wceq.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "rexrd.mm"
include "icc0.mm"
include "syl2anc.mm"
include "biimpar.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "ralrimivw.mm"
include "r19.2z.mm"
include "sylancr.mm"
include "wi.mm"
include "cdv.mm"
include "cima.mm"
include "csup.mm"
include "adantr.mm"
include "simpr.mm"
include "cc.mm"
include "cpm.mm"
include "cres.mm"
include "ccncf.mm"
include "eqid.mm"
include "c1liplem1.mm"
include "oveq1.mm"
include "breq2d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syl.mm"
include "weq.mm"
include "breq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "oveq1d.mm"
include "rspc2v.mm"
include "ad2antlr.mm"
include "pm2.27.mm"
include "adantl.mm"
include "syld.mm"
include "0le0.mm"
include "fvres.mm"
include "ad2antrl.mm"
include "wf.mm"
include "cncff.mm"
include "ad2antrr.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "eqeltrrd.mm"
include "recnd.mm"
include "subidd.mm"
include "abs00bd.mm"
include "wss.mm"
include "iccssre.mm"
include "ad3antrrr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simplr.mm"
include "mul01d.mm"
include "eqtrd.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "a1d.mm"
include "ancoms.mm"
include "ad2antll.mm"
include "abssubd.mm"
include "sseld.mm"
include "anim12d.mm"
include "recn.mm"
include "abssub.mm"
include "biimpd.mm"
include "embantd.mm"
include "w3o.mm"
include "lttri4.mm"
include "mpjao3dan.mm"
include "ralrimdvva.mm"
include "reximdva.mm"
include "mpd.mm"
include "ltlecasei.mm"

theorem c1lip1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let va: setvar a
  let vb: setvar b
  assume c1lip1.a: |- ( ph -> A e. RR )
  assume c1lip1.b: |- ( ph -> B e. RR )
  assume c1lip1.f: |- ( ph -> F e. ( CC ^pm RR ) )
  assume c1lip1.dv: |- ( ph -> ( ( RR _D F ) |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) )
  assume c1lip1.cn: |- ( ph -> ( F |` ( A [,] B ) ) e. ( ( A [,] B ) -cn-> RR ) )

  disjoint ph x
  disjoint ph y
  disjoint k ph
  disjoint x y
  disjoint k x
  disjoint k y
  disjoint A x
  disjoint A y
  disjoint A k
  disjoint B x
  disjoint B y
  disjoint B k
  disjoint F x
  disjoint F y
  disjoint F k
  disjoint a ph
  disjoint b ph
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint a k
  disjoint b k
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint F a
  disjoint F b
  assert |- ( ph -> E. k e. RR A. x e. ( A [,] B ) A. y e. ( A [,] B ) ( abs ` ( ( F ` y ) - ( F ` x ) ) ) <_ ( k x. ( abs ` ( y - x ) ) ) )

  proof
    wph
    vy
    cv
    #
    cF
    cfv
    #
    vx
    cv
    #
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vk
    cv
    #
    @0
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cA
    cB
    cicc
    co
    #
    wral
    #
    vx
    @11
    wral
    #
    vk
    cr
    wrex
    #
    cB
    cA
    wph
    cB
    cA
    clt
    wbr
    #
    wa
    #
    cr
    c0
    wne
    @13
    vk
    cr
    wral
    @14
    cc0
    cr
    0re
    ne0ii
    @16
    @13
    vk
    cr
    @16
    @13
    @12
    vx
    c0
    wral
    @12
    vx
    ral0
    @16
    @12
    vx
    @11
    c0
    wph
    @11
    c0
    wceq
    #
    @15
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    @17
    @15
    wb
    wph
    cA
    c1lip1.a
    rexrd
    wph
    cB
    c1lip1.b
    rexrd
    cA
    cB
    icc0
    syl2anc
    biimpar
    raleqdv
    mpbiri
    ralrimivw
    @13
    vk
    cr
    r19.2z
    sylancr
    wph
    cA
    cB
    cle
    wbr
    #
    wa
    #
    va
    cv
    #
    vb
    cv
    #
    clt
    wbr
    #
    @21
    cF
    cfv
    #
    @20
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    @21
    @20
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    vb
    @11
    wral
    va
    @11
    wral
    #
    vk
    cr
    wrex
    #
    @14
    @19
    cabs
    cr
    cF
    cdv
    co
    #
    @11
    cima
    cima
    cr
    clt
    csup
    #
    cr
    wcel
    @22
    @26
    @35
    @28
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    vb
    @11
    wral
    va
    @11
    wral
    #
    wa
    @33
    @19
    va
    vb
    cA
    cB
    cF
    @35
    wph
    cA
    cr
    wcel
    #
    @18
    c1lip1.a
    adantr
    wph
    cB
    cr
    wcel
    #
    @18
    c1lip1.b
    adantr
    wph
    @18
    simpr
    wph
    cF
    cc
    cr
    cpm
    co
    wcel
    @18
    c1lip1.f
    adantr
    wph
    @34
    @11
    cres
    @11
    cr
    ccncf
    co
    #
    wcel
    @18
    c1lip1.dv
    adantr
    wph
    cF
    @11
    cres
    #
    @42
    wcel
    #
    @18
    c1lip1.cn
    adantr
    @35
    eqid
    c1liplem1
    @32
    @39
    vk
    @35
    cr
    @6
    @35
    wceq
    #
    @31
    @38
    va
    vb
    @11
    @11
    @45
    @30
    @37
    @22
    @45
    @29
    @36
    @26
    cle
    @6
    @35
    @28
    cmul
    oveq1
    breq2d
    imbi2d
    2ralbidv
    rspcev
    syl
    @19
    @32
    @13
    vk
    cr
    @19
    @6
    cr
    wcel
    #
    wa
    #
    @32
    @10
    vx
    vy
    @11
    @11
    @47
    @2
    @11
    wcel
    #
    @0
    @11
    wcel
    #
    wa
    #
    wa
    #
    @2
    @0
    clt
    wbr
    #
    @32
    @10
    wi
    vx
    vy
    weq
    #
    @0
    @2
    clt
    wbr
    #
    @51
    @52
    wa
    @32
    @52
    @10
    wi
    #
    @10
    @50
    @32
    @55
    wi
    @47
    @52
    @31
    @55
    @2
    @21
    clt
    wbr
    #
    @23
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    @21
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    va
    vb
    @2
    @0
    @11
    @11
    va
    vx
    weq
    #
    @22
    @56
    @30
    @62
    @20
    @2
    @21
    clt
    breq1
    @63
    @26
    @58
    @29
    @61
    cle
    @63
    @25
    @57
    cabs
    @63
    @24
    @3
    @23
    cmin
    @20
    @2
    cF
    fveq2
    oveq2d
    fveq2d
    @63
    @28
    @60
    @6
    cmul
    @63
    @27
    @59
    cabs
    @20
    @2
    @21
    cmin
    oveq2
    fveq2d
    oveq2d
    breq12d
    imbi12d
    vb
    vy
    weq
    #
    @56
    @52
    @62
    @10
    @21
    @0
    @2
    clt
    breq2
    @64
    @58
    @5
    @61
    @9
    cle
    @64
    @57
    @4
    cabs
    @64
    @23
    @1
    @3
    cmin
    @21
    @0
    cF
    fveq2
    oveq1d
    fveq2d
    @64
    @60
    @8
    @6
    cmul
    @64
    @59
    @7
    cabs
    @21
    @0
    @2
    cmin
    oveq1
    fveq2d
    oveq2d
    breq12d
    imbi12d
    rspc2v
    ad2antlr
    @52
    @55
    @10
    wi
    @51
    @52
    @10
    pm2.27
    adantl
    syld
    @51
    @53
    wa
    @10
    @32
    @51
    @53
    @10
    @51
    @3
    @3
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    @2
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @53
    @10
    @51
    @70
    cc0
    cc0
    cle
    wbr
    0le0
    @51
    @66
    cc0
    @69
    cc0
    cle
    @51
    @65
    @51
    @3
    @51
    @3
    @51
    @2
    @43
    cfv
    #
    @3
    cr
    @48
    @71
    @3
    wceq
    @47
    @49
    @2
    @11
    cF
    fvres
    ad2antrl
    @47
    @11
    cr
    @43
    wf
    #
    @48
    @71
    cr
    wcel
    @50
    wph
    @72
    @18
    @46
    wph
    @44
    @72
    c1lip1.cn
    @11
    cr
    @43
    cncff
    syl
    ad2antrr
    #
    @48
    @49
    simpl
    @11
    cr
    @2
    @43
    ffvelrn
    syl2an
    eqeltrrd
    recnd
    #
    subidd
    abs00bd
    @51
    @69
    @6
    cc0
    cmul
    co
    cc0
    @51
    @68
    cc0
    @6
    cmul
    @51
    @67
    @51
    @2
    @51
    @2
    @51
    @11
    cr
    @2
    wph
    @11
    cr
    wss
    #
    @18
    @46
    @50
    wph
    @40
    @41
    @75
    c1lip1.a
    c1lip1.b
    cA
    cB
    iccssre
    syl2anc
    #
    ad3antrrr
    @47
    @48
    @49
    simprl
    sseldd
    recnd
    subidd
    abs00bd
    oveq2d
    @51
    @6
    @51
    @6
    @19
    @46
    @50
    simplr
    recnd
    mul01d
    eqtrd
    breq12d
    mpbiri
    @53
    @66
    @5
    @69
    @9
    cle
    @53
    @65
    @4
    cabs
    @53
    @3
    @1
    @3
    cmin
    @2
    @0
    cF
    fveq2
    oveq1d
    fveq2d
    @53
    @68
    @8
    @6
    cmul
    @53
    @67
    @7
    cabs
    @2
    @0
    @2
    cmin
    oveq1
    fveq2d
    oveq2d
    breq12d
    syl5ibcom
    imp
    a1d
    @51
    @54
    wa
    #
    @32
    @54
    @3
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    @2
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    #
    @10
    @50
    @32
    @84
    wi
    #
    @47
    @54
    @49
    @48
    @85
    @31
    @84
    @0
    @21
    clt
    wbr
    #
    @23
    @1
    cmin
    co
    #
    cabs
    cfv
    #
    @6
    @21
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    wi
    va
    vb
    @0
    @2
    @11
    @11
    va
    vy
    weq
    #
    @22
    @86
    @30
    @92
    @20
    @0
    @21
    clt
    breq1
    @93
    @26
    @88
    @29
    @91
    cle
    @93
    @25
    @87
    cabs
    @93
    @24
    @1
    @23
    cmin
    @20
    @0
    cF
    fveq2
    oveq2d
    fveq2d
    @93
    @28
    @90
    @6
    cmul
    @93
    @27
    @89
    cabs
    @20
    @0
    @21
    cmin
    oveq2
    fveq2d
    oveq2d
    breq12d
    imbi12d
    vb
    vx
    weq
    #
    @86
    @54
    @92
    @83
    @21
    @2
    @0
    clt
    breq2
    @94
    @88
    @79
    @91
    @82
    cle
    @94
    @87
    @78
    cabs
    @94
    @23
    @3
    @1
    cmin
    @21
    @2
    cF
    fveq2
    oveq1d
    fveq2d
    @94
    @90
    @81
    @6
    cmul
    @94
    @89
    @80
    cabs
    @21
    @2
    @0
    cmin
    oveq1
    fveq2d
    oveq2d
    breq12d
    imbi12d
    rspc2v
    ancoms
    ad2antlr
    @77
    @54
    @83
    @10
    @51
    @54
    simpr
    @77
    @83
    @10
    @77
    @79
    @5
    @82
    @9
    cle
    @51
    @79
    @5
    wceq
    @54
    @51
    @3
    @1
    @74
    @51
    @1
    @51
    @0
    @43
    cfv
    #
    @1
    cr
    @49
    @95
    @1
    wceq
    @47
    @48
    @0
    @11
    cF
    fvres
    ad2antll
    @47
    @72
    @49
    @95
    cr
    wcel
    @50
    @73
    @48
    @49
    simpr
    @11
    cr
    @0
    @43
    ffvelrn
    syl2an
    eqeltrrd
    recnd
    abssubd
    adantr
    @77
    @81
    @8
    @6
    cmul
    @51
    @81
    @8
    wceq
    #
    @54
    @51
    @2
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    wa
    #
    @96
    @47
    @50
    @99
    @47
    @48
    @97
    @49
    @98
    @47
    @11
    cr
    @2
    wph
    @75
    @18
    @46
    @76
    ad2antrr
    #
    sseld
    @47
    @11
    cr
    @0
    @100
    sseld
    anim12d
    imp
    #
    @97
    @2
    cc
    wcel
    @0
    cc
    wcel
    @96
    @98
    @2
    recn
    @0
    recn
    @2
    @0
    abssub
    syl2an
    syl
    adantr
    oveq2d
    breq12d
    biimpd
    embantd
    syld
    @51
    @99
    @52
    @53
    @54
    w3o
    @101
    @2
    @0
    lttri4
    syl
    mpjao3dan
    ralrimdvva
    reximdva
    mpd
    c1lip1.b
    c1lip1.a
    ltlecasei
end
