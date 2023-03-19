include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "clsp.mm"
include "cr.mm"
include "wcel.mm"
include "c3.mm"
include "cmul.mm"
include "wa.mm"
include "cxr.mm"
include "caddc.mm"
include "cmnf.mm"
include "cvv.mm"
include "wf.mm"
include "wss.mm"
include "reex.mm"
include "ssex.mm"
include "syl.mm"
include "a1i.mm"
include "fex2.mm"
include "syl3anc.mm"
include "limsupcl.mm"
include "adantr.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "rpred.mm"
include "readdcld.mm"
include "mnfxr.mm"
include "resubcld.mm"
include "rexrd.mm"
include "mnfltd.mm"
include "ressxr.mm"
include "fss.mm"
include "sylancl.mm"
include "csup.mm"
include "cpnf.mm"
include "wceq.mm"
include "wrex.mm"
include "sseldd.mm"
include "simprr.mm"
include "breq2.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "ffvelrnda.mm"
include "recnd.mm"
include "abscld.mm"
include "ltle.mm"
include "syl2anc.mm"
include "absdifled.mm"
include "sylibd.mm"
include "simpl.mm"
include "syl6.mm"
include "imim2d.mm"
include "ralimdva.mm"
include "mpd.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "limsupbnd2.mm"
include "xrltletrd.mm"
include "adantrr.mm"
include "simplrr.mm"
include "rspcv.mm"
include "syl3c.mm"
include "ltled.mm"
include "mpbid.mm"
include "simprd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "limsupbnd1.mm"
include "xrre.mm"
include "syl22anc.mm"
include "c2.mm"
include "2re.mm"
include "remulcl.mm"
include "sylancr.mm"
include "3re.mm"
include "abssubd.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "subsub4d.mm"
include "eqtr4d.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "lesub1dd.mm"
include "eqbrtrd.mm"
include "letrd.mm"
include "leadd1dd.mm"
include "addassd.mm"
include "breqtrd.mm"
include "mpbir2and.mm"
include "2lt3.mm"
include "crp.mm"
include "ltmul1d.mm"
include "mpbii.mm"
include "lelttrd.mm"
include "sylibr.mm"
include "jca.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "sylc.mm"
include "reximddv.mm"

theorem caucvgrlem
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cR: class R
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let vm: setvar m
  let vn: setvar n
  let vy: setvar y
  assume caurcvgr.1: |- ( ph -> A C_ RR )
  assume caurcvgr.2: |- ( ph -> F : A --> RR )
  assume caurcvgr.3: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume caurcvgr.4: |- ( ph -> A. x e. RR+ E. j e. A A. k e. A ( j <_ k -> ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) )
  assume caucvgrlem.4: |- ( ph -> R e. RR+ )

  disjoint j k
  disjoint j x
  disjoint A j
  disjoint k x
  disjoint A k
  disjoint A x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint R j
  disjoint R k
  disjoint R x
  disjoint j m
  disjoint j n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint j y
  disjoint k y
  disjoint m y
  disjoint F m
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F y
  disjoint m ph
  disjoint n ph
  disjoint ph y
  disjoint R m
  disjoint R n
  assert |- ( ph -> E. j e. A ( ( limsup ` F ) e. RR /\ A. k e. A ( j <_ k -> ( abs ` ( ( F ` k ) - ( limsup ` F ) ) ) < ( 3 x. R ) ) ) )

  proof
    wph
    vj
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    @1
    cF
    cfv
    #
    @0
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    wi
    #
    vk
    cA
    wral
    #
    cF
    clsp
    cfv
    #
    cr
    wcel
    #
    @2
    @3
    @10
    cmin
    co
    #
    cabs
    cfv
    #
    c3
    cR
    cmul
    co
    #
    clt
    wbr
    #
    wi
    #
    vk
    cA
    wral
    #
    wa
    vj
    cA
    wph
    @0
    cA
    wcel
    #
    @9
    wa
    #
    wa
    #
    @11
    @17
    @20
    @10
    cxr
    wcel
    #
    @4
    cR
    caddc
    co
    #
    cr
    wcel
    #
    cmnf
    @10
    clt
    wbr
    @10
    @22
    cle
    wbr
    #
    @11
    wph
    @21
    @19
    wph
    cF
    cvv
    wcel
    #
    @21
    wph
    cA
    cr
    cF
    wf
    #
    cA
    cvv
    wcel
    #
    cr
    cvv
    wcel
    #
    @25
    caurcvgr.2
    wph
    cA
    cr
    wss
    #
    @27
    caurcvgr.1
    cA
    cr
    reex
    ssex
    syl
    @28
    wph
    reex
    a1i
    cA
    cr
    cF
    cvv
    cvv
    fex2
    syl3anc
    cF
    cvv
    limsupcl
    syl
    adantr
    #
    @20
    @4
    cR
    @20
    cA
    cr
    @0
    cF
    wph
    @26
    @19
    caurcvgr.2
    adantr
    #
    wph
    @18
    @9
    simprl
    #
    ffvelrnd
    #
    wph
    cR
    cr
    wcel
    #
    @19
    wph
    cR
    caucvgrlem.4
    rpred
    adantr
    #
    readdcld
    #
    @20
    cmnf
    @4
    cR
    cmin
    co
    #
    @10
    cmnf
    cxr
    wcel
    @20
    mnfxr
    a1i
    @20
    @37
    @20
    @4
    cR
    @33
    @35
    resubcld
    #
    rexrd
    #
    @30
    @20
    @37
    @38
    mnfltd
    @20
    @37
    cA
    vm
    vn
    cF
    wph
    @29
    @19
    caurcvgr.1
    adantr
    #
    wph
    cA
    cxr
    cF
    wf
    #
    @19
    wph
    @26
    cr
    cxr
    wss
    @41
    caurcvgr.2
    ressxr
    cA
    cr
    cxr
    cF
    fss
    sylancl
    adantr
    #
    @39
    wph
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    @19
    caurcvgr.3
    adantr
    @20
    @0
    cr
    wcel
    #
    @0
    vm
    cv
    #
    cle
    wbr
    #
    @37
    @44
    cF
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vm
    cA
    wral
    #
    vn
    cv
    #
    @44
    cle
    wbr
    #
    @47
    wi
    #
    vm
    cA
    wral
    #
    vn
    cr
    wrex
    @20
    cA
    cr
    @0
    @40
    @32
    sseldd
    #
    @20
    @45
    @46
    @4
    cmin
    co
    #
    cabs
    cfv
    #
    cR
    clt
    wbr
    #
    wi
    #
    vm
    cA
    wral
    #
    @49
    @20
    @9
    @59
    wph
    @18
    @9
    simprr
    @8
    @58
    vk
    vm
    cA
    @1
    @44
    wceq
    #
    @2
    @45
    @7
    @57
    @1
    @44
    @0
    cle
    breq2
    #
    @60
    @6
    @56
    cR
    clt
    @60
    @5
    @55
    cabs
    @60
    @3
    @46
    @4
    cmin
    @1
    @44
    cF
    fveq2
    #
    oveq1d
    fveq2d
    breq1d
    imbi12d
    #
    cbvralv
    sylib
    @20
    @58
    @48
    vm
    cA
    @20
    @44
    cA
    wcel
    #
    wa
    #
    @57
    @47
    @45
    @65
    @57
    @47
    @46
    @22
    cle
    wbr
    #
    wa
    #
    @47
    @65
    @57
    @56
    cR
    cle
    wbr
    #
    @67
    @65
    @56
    cr
    wcel
    #
    @34
    @57
    @68
    wi
    @65
    @55
    @65
    @55
    @65
    @46
    @4
    @20
    cA
    cr
    @44
    cF
    @31
    ffvelrnda
    #
    @20
    @4
    cr
    wcel
    #
    @64
    @33
    adantr
    #
    resubcld
    recnd
    abscld
    #
    @20
    @34
    @64
    @35
    adantr
    #
    @56
    cR
    ltle
    syl2anc
    @65
    @46
    @4
    cR
    @70
    @72
    @74
    absdifled
    sylibd
    @47
    @66
    simpl
    #
    syl6
    imim2d
    ralimdva
    mpd
    @53
    @49
    vn
    @0
    cr
    @50
    @0
    wceq
    #
    @52
    @48
    vm
    cA
    @76
    @51
    @45
    @47
    @50
    @0
    @44
    cle
    breq1
    #
    imbi1d
    ralbidv
    rspcev
    syl2anc
    limsupbnd2
    #
    xrltletrd
    @20
    @22
    cA
    vm
    vn
    cF
    @40
    @42
    @20
    @22
    @36
    rexrd
    @20
    @43
    @45
    @66
    wi
    #
    vm
    cA
    wral
    #
    @51
    @66
    wi
    #
    vm
    cA
    wral
    #
    vn
    cr
    wrex
    @54
    @20
    @79
    vm
    cA
    @20
    @64
    @45
    @66
    @20
    @64
    @45
    wa
    #
    wa
    #
    @47
    @66
    @84
    @68
    @67
    @84
    @56
    cR
    @20
    @64
    @69
    @45
    @73
    adantrr
    @20
    @34
    @83
    @35
    adantr
    #
    @84
    @64
    @9
    @45
    @57
    @20
    @64
    @45
    simprl
    wph
    @18
    @9
    @83
    simplrr
    @20
    @64
    @45
    simprr
    @8
    @58
    vk
    @44
    cA
    @63
    rspcv
    syl3c
    ltled
    @84
    @46
    @4
    cR
    @20
    @64
    @46
    cr
    wcel
    @45
    @70
    adantrr
    #
    @20
    @71
    @83
    @33
    adantr
    #
    @85
    absdifled
    mpbid
    #
    simprd
    #
    expr
    ralrimiva
    @82
    @80
    vn
    @0
    cr
    @76
    @81
    @79
    vm
    cA
    @76
    @51
    @45
    @66
    @77
    imbi1d
    ralbidv
    rspcev
    syl2anc
    limsupbnd1
    #
    @10
    @22
    xrre
    syl22anc
    #
    @20
    @45
    @46
    @10
    cmin
    co
    #
    cabs
    cfv
    #
    @14
    clt
    wbr
    #
    wi
    #
    vm
    cA
    wral
    @17
    @20
    @95
    vm
    cA
    @20
    @64
    @45
    @94
    @84
    @93
    c2
    cR
    cmul
    co
    #
    @14
    @84
    @92
    @84
    @92
    @84
    @46
    @10
    @86
    @20
    @11
    @83
    @91
    adantr
    #
    resubcld
    recnd
    abscld
    @84
    c2
    cr
    wcel
    #
    @34
    @96
    cr
    wcel
    2re
    @85
    c2
    cR
    remulcl
    sylancr
    #
    @84
    c3
    cr
    wcel
    #
    @34
    @14
    cr
    wcel
    3re
    @85
    c3
    cR
    remulcl
    sylancr
    @84
    @93
    @10
    @46
    cmin
    co
    cabs
    cfv
    #
    @96
    cle
    @84
    @46
    @10
    @84
    @46
    @86
    recnd
    #
    @84
    @10
    @97
    recnd
    abssubd
    @84
    @101
    @96
    cle
    wbr
    @46
    @96
    cmin
    co
    #
    @10
    cle
    wbr
    @10
    @46
    @96
    caddc
    co
    #
    cle
    wbr
    @84
    @103
    @37
    @10
    @84
    @46
    @96
    @86
    @99
    resubcld
    @20
    @37
    cr
    wcel
    @83
    @38
    adantr
    @97
    @84
    @103
    @46
    cR
    cmin
    co
    #
    cR
    cmin
    co
    #
    @37
    cle
    @84
    @103
    @46
    cR
    cR
    caddc
    co
    #
    cmin
    co
    @106
    @84
    @96
    @107
    @46
    cmin
    @84
    cR
    @84
    cR
    @85
    recnd
    #
    2timesd
    #
    oveq2d
    @84
    @46
    cR
    cR
    @102
    @108
    @108
    subsub4d
    eqtr4d
    @84
    @105
    @4
    cR
    @84
    @46
    cR
    @86
    @85
    resubcld
    @87
    @85
    @84
    @105
    @4
    cle
    wbr
    @66
    @89
    @84
    @46
    cR
    @4
    @86
    @85
    @87
    lesubaddd
    mpbird
    lesub1dd
    eqbrtrd
    @20
    @37
    @10
    cle
    wbr
    @83
    @78
    adantr
    letrd
    @84
    @10
    @22
    @104
    @97
    @20
    @23
    @83
    @36
    adantr
    @84
    @46
    @96
    @86
    @99
    readdcld
    @20
    @24
    @83
    @90
    adantr
    @84
    @22
    @46
    cR
    caddc
    co
    #
    cR
    caddc
    co
    #
    @104
    cle
    @84
    @4
    @110
    cR
    @87
    @84
    @46
    cR
    @86
    @85
    readdcld
    @85
    @84
    @47
    @4
    @110
    cle
    wbr
    @84
    @67
    @47
    @88
    @75
    syl
    @84
    @4
    cR
    @46
    @87
    @85
    @86
    lesubaddd
    mpbid
    leadd1dd
    @84
    @111
    @46
    @107
    caddc
    co
    @104
    @84
    @46
    cR
    cR
    @102
    @108
    @108
    addassd
    @84
    @96
    @107
    @46
    caddc
    @109
    oveq2d
    eqtr4d
    breqtrd
    letrd
    @84
    @10
    @46
    @96
    @97
    @86
    @99
    absdifled
    mpbir2and
    eqbrtrd
    @84
    c2
    c3
    clt
    wbr
    @96
    @14
    clt
    wbr
    2lt3
    @84
    c2
    c3
    cR
    @98
    @84
    2re
    a1i
    @100
    @84
    3re
    a1i
    @20
    cR
    crp
    wcel
    #
    @83
    wph
    @112
    @19
    caucvgrlem.4
    adantr
    adantr
    ltmul1d
    mpbii
    lelttrd
    expr
    ralrimiva
    @16
    @95
    vk
    vm
    cA
    @60
    @2
    @45
    @15
    @94
    @61
    @60
    @13
    @93
    @14
    clt
    @60
    @12
    @92
    cabs
    @60
    @3
    @46
    @10
    cmin
    @62
    oveq1d
    fveq2d
    breq1d
    imbi12d
    cbvralv
    sylibr
    jca
    wph
    @112
    @2
    @6
    vx
    cv
    #
    clt
    wbr
    #
    wi
    #
    vk
    cA
    wral
    vj
    cA
    wrex
    #
    vx
    crp
    wral
    @9
    vj
    cA
    wrex
    #
    caucvgrlem.4
    caurcvgr.4
    @116
    @117
    vx
    cR
    crp
    @113
    cR
    wceq
    #
    @115
    @8
    vj
    vk
    cA
    cA
    @118
    @114
    @7
    @2
    @113
    cR
    @6
    clt
    breq2
    imbi2d
    rexralbidv
    rspcv
    sylc
    reximddv
end
