include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cmin.mm"
include "wi.mm"
include "cc.mm"
include "wral.mm"
include "wrex.mm"
include "cc0.mm"
include "cfz.mm"
include "csu.mm"
include "cdiv.mm"
include "fzfid.mm"
include "wa.mm"
include "cn0.mm"
include "wf.mm"
include "cply.mm"
include "coef3.mm"
include "syl.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "abscld.mm"
include "fsumrecl.mm"
include "rerpdivcld.mm"
include "syl5eqel.mm"
include "1re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "caddc.mm"
include "wceq.mm"
include "adantr.mm"
include "simprl.mm"
include "coeid2.mm"
include "syl2anc.mm"
include "cuz.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "sylan.mm"
include "expcl.mm"
include "mulcld.mm"
include "sylan2.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "fsumm1.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "fsumcl.mm"
include "ffvelrnd.mm"
include "expcld.mm"
include "pncand.mm"
include "fveq2d.mm"
include "crp.mm"
include "rpred.mm"
include "reexpcld.mm"
include "remulcld.mm"
include "fsumabs.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "adantlr.mm"
include "absmuld.mm"
include "absge0d.mm"
include "absexp.mm"
include "a1i.mm"
include "max1.mm"
include "sylancr.mm"
include "simprr.mm"
include "lelttrd.mm"
include "ltled.mm"
include "elfzuz3.mm"
include "adantl.mm"
include "leexp2ad.mm"
include "eqbrtrd.mm"
include "lemul2ad.mm"
include "fsumle.mm"
include "recnd.mm"
include "fsummulc1.mm"
include "breqtrrd.mm"
include "max2.mm"
include "syl5eqbrr.mm"
include "ltdivmuld.mm"
include "mpbid.mm"
include "wb.mm"
include "cz.mm"
include "nn0zd.mm"
include "0red.mm"
include "0lt1.mm"
include "lttrd.mm"
include "expgt0.mm"
include "syl3anc.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "expm1t.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "expr.mm"
include "ralrimiva.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"

theorem ftalem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cE: class E
  let cF: class F
  let cN: class N
  let vr: setvar r
  let vn: setvar n
  let vs: setvar s
  let vz: setvar z
  let cD: class D
  let cK: class K
  let vw: setvar w
  let vy: setvar y
  let cJ: class J
  let cR: class R
  let cU: class U
  let cX: class X
  assume ftalem.1: |- A = ( coeff ` F )
  assume ftalem.2: |- N = ( deg ` F )
  assume ftalem.3: |- ( ph -> F e. ( Poly ` S ) )
  assume ftalem.4: |- ( ph -> N e. NN )
  assume ftalem1.5: |- ( ph -> E e. RR+ )
  assume ftalem1.6: |- T = ( sum_ k e. ( 0 ... ( N - 1 ) ) ( abs ` ( A ` k ) ) / E )

  disjoint k r
  disjoint k x
  disjoint A k
  disjoint r x
  disjoint A r
  disjoint A x
  disjoint E r
  disjoint N k
  disjoint N r
  disjoint N x
  disjoint F k
  disjoint F r
  disjoint F x
  disjoint k ph
  disjoint ph x
  disjoint S k
  disjoint T k
  disjoint T r
  disjoint T x
  disjoint k n
  disjoint k s
  disjoint n r
  disjoint n s
  disjoint n x
  disjoint A n
  disjoint r s
  disjoint s x
  disjoint A s
  disjoint s z
  disjoint D s
  disjoint x z
  disjoint D x
  disjoint D z
  disjoint K k
  disjoint K n
  disjoint N n
  disjoint N s
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint s w
  disjoint s y
  disjoint F s
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J s
  disjoint J x
  disjoint J z
  disjoint ph s
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint S s
  disjoint U r
  disjoint U x
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> E. r e. RR A. x e. CC ( r < ( abs ` x ) -> ( abs ` ( ( F ` x ) - ( ( A ` N ) x. ( x ^ N ) ) ) ) < ( E x. ( ( abs ` x ) ^ N ) ) ) )

  proof
    wph
    c1
    cT
    cle
    wbr
    #
    cT
    c1
    cif
    #
    cr
    wcel
    #
    @1
    vx
    cv
    #
    cabs
    cfv
    #
    clt
    wbr
    #
    @3
    cF
    cfv
    #
    cN
    cA
    cfv
    #
    @3
    cN
    cexp
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cabs
    cfv
    #
    cE
    @4
    cN
    cexp
    co
    #
    cmul
    co
    #
    clt
    wbr
    #
    wi
    #
    vx
    cc
    wral
    #
    vr
    cv
    #
    @4
    clt
    wbr
    #
    @14
    wi
    #
    vx
    cc
    wral
    #
    vr
    cr
    wrex
    wph
    cT
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    @2
    wph
    cT
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    cabs
    cfv
    #
    vk
    csu
    #
    cE
    cdiv
    co
    #
    cr
    ftalem1.6
    wph
    @28
    cE
    wph
    @24
    @27
    vk
    wph
    cc0
    @23
    fzfid
    wph
    @25
    @24
    wcel
    #
    wa
    @26
    wph
    cn0
    cc
    cA
    wf
    #
    @25
    cn0
    wcel
    #
    @26
    cc
    wcel
    #
    @30
    wph
    cF
    cS
    cply
    cfv
    wcel
    #
    @31
    ftalem.3
    cA
    cS
    cF
    ftalem.1
    coef3
    syl
    #
    @25
    @23
    elfznn0
    #
    cn0
    cc
    @25
    cA
    ffvelrn
    #
    syl2an
    abscld
    #
    fsumrecl
    #
    ftalem1.5
    rerpdivcld
    syl5eqel
    #
    1re
    @0
    cT
    c1
    cr
    ifcl
    sylancl
    #
    wph
    @15
    vx
    cc
    wph
    @3
    cc
    wcel
    #
    @5
    @14
    wph
    @42
    @5
    wa
    #
    wa
    #
    @11
    @24
    @26
    @3
    @25
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cabs
    cfv
    #
    @13
    clt
    @44
    @10
    @47
    cabs
    @44
    @10
    @47
    @9
    caddc
    co
    #
    @9
    cmin
    co
    @47
    @44
    @6
    @49
    @9
    cmin
    @44
    @6
    cc0
    cN
    cfz
    co
    #
    @46
    vk
    csu
    #
    @49
    @44
    @34
    @42
    @6
    @51
    wceq
    wph
    @34
    @43
    ftalem.3
    adantr
    wph
    @42
    @5
    simprl
    #
    cA
    cS
    vk
    cF
    cN
    @3
    ftalem.1
    ftalem.2
    coeid2
    syl2anc
    @44
    @46
    @9
    vk
    cc0
    cN
    @44
    cN
    cn0
    cc0
    cuz
    cfv
    wph
    cN
    cn0
    wcel
    @43
    wph
    cN
    ftalem.4
    nnnn0d
    adantr
    #
    nn0uz
    syl6eleq
    @25
    @50
    wcel
    @44
    @32
    @46
    cc
    wcel
    #
    @25
    cN
    elfznn0
    @44
    @32
    wa
    #
    @26
    @45
    @44
    @31
    @32
    @33
    wph
    @31
    @43
    @35
    adantr
    #
    @37
    sylan
    #
    @44
    @42
    @32
    @45
    cc
    wcel
    #
    @52
    @3
    @25
    expcl
    sylan
    #
    mulcld
    #
    sylan2
    @25
    cN
    wceq
    @26
    @7
    @45
    @8
    cmul
    @25
    cN
    cA
    fveq2
    @25
    cN
    @3
    cexp
    oveq2
    oveq12d
    fsumm1
    eqtrd
    oveq1d
    @44
    @47
    @9
    @44
    @24
    @46
    vk
    @44
    cc0
    @23
    fzfid
    #
    @30
    @44
    @32
    @54
    @36
    @60
    sylan2
    #
    fsumcl
    #
    @44
    @7
    @8
    @44
    cn0
    cc
    cN
    cA
    @56
    @53
    ffvelrnd
    @44
    @3
    cN
    @52
    @53
    expcld
    mulcld
    pncand
    eqtrd
    fveq2d
    @44
    @48
    @24
    @46
    cabs
    cfv
    #
    vk
    csu
    #
    @13
    @44
    @47
    @63
    abscld
    @44
    @24
    @64
    vk
    @61
    @44
    @30
    wa
    #
    @46
    @62
    abscld
    #
    fsumrecl
    #
    @44
    cE
    @12
    @44
    cE
    wph
    cE
    crp
    wcel
    @43
    ftalem1.5
    adantr
    #
    rpred
    #
    @44
    @4
    cN
    @44
    @3
    @52
    abscld
    #
    @53
    reexpcld
    remulcld
    #
    @44
    @24
    @46
    vk
    @61
    @62
    fsumabs
    @44
    @65
    @28
    @4
    @23
    cexp
    co
    #
    cmul
    co
    #
    @13
    @68
    @44
    @28
    @73
    wph
    @28
    cr
    wcel
    #
    @43
    @39
    adantr
    #
    @44
    @4
    @23
    @71
    @44
    cN
    cn
    wcel
    #
    @23
    cn0
    wcel
    wph
    @77
    @43
    ftalem.4
    adantr
    #
    cN
    nnm1nn0
    syl
    #
    reexpcld
    #
    remulcld
    @72
    @44
    @65
    @24
    @27
    @73
    cmul
    co
    #
    vk
    csu
    @74
    cle
    @44
    @24
    @64
    @81
    vk
    @61
    @67
    @66
    @27
    @73
    wph
    @30
    @27
    cr
    wcel
    @43
    @38
    adantlr
    #
    @44
    @73
    cr
    wcel
    #
    @30
    @80
    adantr
    #
    remulcld
    @66
    @64
    @27
    @45
    cabs
    cfv
    #
    cmul
    co
    #
    @81
    cle
    @30
    @44
    @32
    @64
    @86
    wceq
    @36
    @55
    @26
    @45
    @57
    @59
    absmuld
    sylan2
    @66
    @85
    @73
    @27
    @66
    @45
    @30
    @44
    @32
    @58
    @36
    @59
    sylan2
    abscld
    @84
    @82
    @66
    @26
    @30
    @44
    @32
    @33
    @36
    @57
    sylan2
    absge0d
    @66
    @85
    @4
    @25
    cexp
    co
    #
    @73
    cle
    @44
    @42
    @32
    @85
    @87
    wceq
    @30
    @52
    @36
    @3
    @25
    absexp
    syl2an
    @66
    @4
    @25
    @23
    @44
    @4
    cr
    wcel
    #
    @30
    @71
    adantr
    @44
    c1
    @4
    cle
    wbr
    @30
    @44
    c1
    @4
    @22
    @44
    1re
    a1i
    #
    @71
    @44
    c1
    @1
    @4
    @89
    wph
    @2
    @43
    @41
    adantr
    #
    @71
    wph
    c1
    @1
    cle
    wbr
    #
    @43
    wph
    @22
    @21
    @91
    1re
    @40
    c1
    cT
    max1
    sylancr
    adantr
    wph
    @42
    @5
    simprr
    #
    lelttrd
    #
    ltled
    adantr
    @30
    @23
    @25
    cuz
    cfv
    wcel
    @44
    @25
    cc0
    @23
    elfzuz3
    adantl
    leexp2ad
    eqbrtrd
    lemul2ad
    eqbrtrd
    fsumle
    @44
    @24
    @27
    @73
    vk
    @61
    @44
    @73
    @80
    recnd
    #
    @66
    @27
    @82
    recnd
    fsummulc1
    breqtrrd
    @44
    @74
    cE
    @4
    cmul
    co
    #
    @73
    cmul
    co
    #
    @13
    clt
    @44
    @28
    @95
    clt
    wbr
    #
    @74
    @96
    clt
    wbr
    #
    @44
    @29
    @4
    clt
    wbr
    @97
    @44
    @29
    cT
    @4
    clt
    ftalem1.6
    @44
    cT
    @1
    @4
    wph
    @21
    @43
    @40
    adantr
    @90
    @71
    wph
    cT
    @1
    cle
    wbr
    #
    @43
    wph
    @22
    @21
    @99
    1re
    @40
    c1
    cT
    max2
    sylancr
    adantr
    @92
    lelttrd
    syl5eqbrr
    @44
    @28
    @4
    cE
    @76
    @71
    @69
    ltdivmuld
    mpbid
    @44
    @75
    @95
    cr
    wcel
    @83
    cc0
    @73
    clt
    wbr
    #
    @97
    @98
    wb
    @76
    @44
    cE
    @4
    @70
    @71
    remulcld
    @80
    @44
    @88
    @23
    cz
    wcel
    cc0
    @4
    clt
    wbr
    @100
    @71
    @44
    @23
    @79
    nn0zd
    @44
    cc0
    c1
    @4
    @44
    0red
    @89
    @71
    cc0
    c1
    clt
    wbr
    @44
    0lt1
    a1i
    @93
    lttrd
    @4
    @23
    expgt0
    syl3anc
    @28
    @95
    @73
    ltmul1
    syl112anc
    mpbid
    @44
    @13
    cE
    @4
    @73
    cmul
    co
    #
    cmul
    co
    @96
    @44
    @12
    @101
    cE
    cmul
    @44
    @12
    @73
    @4
    cmul
    co
    #
    @101
    @44
    @4
    cc
    wcel
    @77
    @12
    @102
    wceq
    @44
    @4
    @71
    recnd
    #
    @78
    @4
    cN
    expm1t
    syl2anc
    @44
    @73
    @4
    @94
    @103
    mulcomd
    eqtrd
    oveq2d
    @44
    cE
    @4
    @73
    @44
    cE
    @70
    recnd
    @103
    @94
    mulassd
    eqtr4d
    breqtrrd
    lelttrd
    lelttrd
    eqbrtrd
    expr
    ralrimiva
    @20
    @16
    vr
    @1
    cr
    @17
    @1
    wceq
    #
    @19
    @15
    vx
    cc
    @104
    @18
    @5
    @14
    @17
    @1
    @4
    clt
    breq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
end
