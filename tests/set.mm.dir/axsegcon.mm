include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wrex.mm"
include "cn.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "cc0.mm"
include "cicc.mm"
include "wi.mm"
include "axsegconlem1.mm"
include "ex.mm"
include "wne.mm"
include "simprll.mm"
include "simprlr.mm"
include "simpl.mm"
include "simprr.mm"
include "w3a.mm"
include "csqrt.mm"
include "cdiv.mm"
include "cmpt.mm"
include "eqid.mm"
include "axsegconlem8.mm"
include "axsegconlem7.mm"
include "axsegconlem10.mm"
include "axsegconlem9.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "oveq1d.mm"
include "sumeq2sdv.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "anbi1d.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "syl31anc.mm"
include "pm2.61ine.mm"
include "wb.mm"
include "simpllr.mm"
include "simplll.mm"
include "simpr.mm"
include "brbtwn.mm"
include "syl3anc.mm"
include "simplrl.mm"
include "simplrr.mm"
include "brcgr.mm"
include "syl22anc.mm"
include "r19.41v.mm"
include "syl6bbr.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "3adant1.mm"

theorem axsegcon
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  let vk: setvar k
  let vp: setvar p
  let vt: setvar t
  let vi: setvar i

  disjoint N x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint N k
  disjoint N p
  disjoint N t
  disjoint N i
  disjoint k p
  disjoint k t
  disjoint i k
  disjoint k x
  disjoint p t
  disjoint i p
  disjoint p x
  disjoint i t
  disjoint t x
  disjoint i x
  disjoint A k
  disjoint A p
  disjoint A t
  disjoint A i
  disjoint B k
  disjoint B p
  disjoint B t
  disjoint B i
  disjoint C k
  disjoint C p
  disjoint C t
  disjoint C i
  disjoint D k
  disjoint D p
  disjoint D t
  disjoint D i
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) ) ) -> E. x e. ( EE ` N ) ( B Btwn <. A , x >. /\ <. B , x >. Cgr <. C , D >. ) )

  proof
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cC
    @0
    wcel
    #
    cD
    @0
    wcel
    #
    wa
    #
    cB
    cA
    vx
    cv
    #
    cop
    cbtwn
    wbr
    #
    cB
    @7
    cop
    cC
    cD
    cop
    ccgr
    wbr
    #
    wa
    #
    vx
    @0
    wrex
    #
    cN
    cn
    wcel
    @3
    @6
    wa
    #
    @11
    vi
    cv
    #
    cB
    cfv
    #
    c1
    vt
    cv
    #
    cmin
    co
    #
    @13
    cA
    cfv
    #
    cmul
    co
    #
    @15
    @13
    @7
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    @23
    @14
    @19
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @23
    @13
    cC
    cfv
    @13
    cD
    cfv
    cmin
    co
    c2
    cexp
    co
    vi
    csu
    #
    wceq
    #
    wa
    #
    vt
    cc0
    c1
    cicc
    co
    #
    wrex
    #
    vx
    @0
    wrex
    #
    @12
    @33
    wi
    cA
    cB
    cA
    cB
    wceq
    @12
    @33
    vx
    vt
    cA
    cB
    cC
    cD
    vi
    cN
    axsegconlem1
    ex
    cA
    cB
    wne
    #
    @12
    @33
    @34
    @12
    wa
    @1
    @2
    @34
    @6
    @33
    @34
    @1
    @2
    @6
    simprll
    @34
    @1
    @2
    @6
    simprlr
    @34
    @12
    simpl
    @34
    @3
    @6
    simprr
    @1
    @2
    @34
    w3a
    @6
    wa
    vk
    @23
    @23
    vp
    cv
    #
    cA
    cfv
    @35
    cB
    cfv
    cmin
    co
    c2
    cexp
    co
    vp
    csu
    #
    csqrt
    cfv
    #
    @23
    @35
    cC
    cfv
    @35
    cD
    cfv
    cmin
    co
    c2
    cexp
    co
    vp
    csu
    #
    csqrt
    cfv
    #
    caddc
    co
    #
    vk
    cv
    #
    cB
    cfv
    cmul
    co
    @39
    @41
    cA
    cfv
    cmul
    co
    cmin
    co
    @37
    cdiv
    co
    cmpt
    #
    @0
    wcel
    @37
    @40
    cdiv
    co
    #
    @31
    wcel
    @14
    c1
    @43
    cmin
    co
    #
    @17
    cmul
    co
    #
    @43
    @13
    @42
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @23
    wral
    #
    @23
    @14
    @46
    cmin
    co
    #
    c2
    cexp
    co
    #
    vi
    csu
    #
    @28
    wceq
    #
    @33
    cA
    cB
    cC
    cD
    @36
    @38
    vk
    @42
    cN
    vp
    @36
    eqid
    #
    @38
    eqid
    #
    @42
    eqid
    #
    axsegconlem8
    cA
    cB
    cC
    cD
    @36
    @38
    cN
    vp
    @55
    @56
    axsegconlem7
    cA
    cB
    cC
    cD
    @36
    @38
    vi
    vk
    @42
    cN
    vp
    @55
    @56
    @57
    axsegconlem10
    cA
    cB
    cC
    cD
    @36
    @38
    vi
    vk
    @42
    cN
    vp
    @55
    @56
    @57
    axsegconlem9
    @30
    @50
    @54
    wa
    @14
    @18
    @15
    @46
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @23
    wral
    #
    @54
    wa
    vx
    vt
    @42
    @43
    @0
    @31
    @7
    @42
    wceq
    #
    @24
    @61
    @29
    @54
    @62
    @22
    @60
    vi
    @23
    @62
    @21
    @59
    @14
    @62
    @20
    @58
    @18
    caddc
    @62
    @19
    @46
    @15
    cmul
    @13
    @7
    @42
    fveq1
    #
    oveq2d
    oveq2d
    eqeq2d
    ralbidv
    @62
    @27
    @53
    @28
    @62
    @23
    @26
    @52
    vi
    @62
    @25
    @51
    c2
    cexp
    @62
    @19
    @46
    @14
    cmin
    @63
    oveq2d
    oveq1d
    sumeq2sdv
    eqeq1d
    anbi12d
    @15
    @43
    wceq
    #
    @61
    @50
    @54
    @64
    @60
    @49
    vi
    @23
    @64
    @59
    @48
    @14
    @64
    @18
    @45
    @58
    @47
    caddc
    @64
    @16
    @44
    @17
    cmul
    @15
    @43
    c1
    cmin
    oveq2
    oveq1d
    @15
    @43
    @46
    cmul
    oveq1
    oveq12d
    eqeq2d
    ralbidv
    anbi1d
    rspc2ev
    syl112anc
    syl31anc
    ex
    pm2.61ine
    @12
    @10
    @32
    vx
    @0
    @12
    @7
    @0
    wcel
    #
    wa
    #
    @10
    @24
    vt
    @31
    wrex
    #
    @29
    wa
    @32
    @66
    @8
    @67
    @9
    @29
    @66
    @2
    @1
    @65
    @8
    @67
    wb
    @1
    @2
    @6
    @65
    simpllr
    #
    @1
    @2
    @6
    @65
    simplll
    @12
    @65
    simpr
    #
    vt
    cB
    cA
    @7
    vi
    cN
    brbtwn
    syl3anc
    @66
    @2
    @65
    @4
    @5
    @9
    @29
    wb
    @68
    @69
    @3
    @4
    @5
    @65
    simplrl
    @3
    @4
    @5
    @65
    simplrr
    cB
    @7
    cC
    cD
    vi
    cN
    brcgr
    syl22anc
    anbi12d
    @24
    @29
    vt
    @31
    r19.41v
    syl6bbr
    rexbidva
    mpbird
    3adant1
end
