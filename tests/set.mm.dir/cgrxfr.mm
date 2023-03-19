include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "cv.mm"
include "ccgr3.mm"
include "wrex.mm"
include "wne.mm"
include "simpl1.mm"
include "simpl3r.mm"
include "simpl3l.mm"
include "btwndiff.mm"
include "syl3anc.mm"
include "wi.mm"
include "simpr.mm"
include "simpl21.mm"
include "simpl22.mm"
include "axsegcon.mm"
include "syl122anc.mm"
include "adantr.mm"
include "anass.mm"
include "simprl.mm"
include "simprr.mm"
include "simpl23.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "wceq.mm"
include "simplrr.mm"
include "ad2antrl.mm"
include "necomd.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "simprrl.mm"
include "btwnexchand.mm"
include "btwnexch3and.mm"
include "simplll.mm"
include "simprrr.mm"
include "cgrextendand.mm"
include "jca.mm"
include "simplrl.mm"
include "btwncomand.mm"
include "simpllr.mm"
include "cgrcomand.mm"
include "3jca.mm"
include "ex.mm"
include "segconeq.mm"
include "syl133anc.mm"
include "syld.mm"
include "imp.mm"
include "opeq2.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "biimpa.mm"
include "simpl.mm"
include "btwnexch3.mm"
include "syl2ani.mm"
include "adantl.mm"
include "wb.mm"
include "brcgr3.mm"
include "mpbir3and.mm"
include "expr.mm"
include "syl5.mm"
include "expcomd.mm"
include "impr.mm"
include "mpd.mm"
include "sylanb.mm"
include "an32s.mm"
include "rexlimdva.mm"
include "reximdva.mm"

theorem cgrxfr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let ve: setvar e
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vg: setvar g

  disjoint A e
  disjoint B e
  disjoint C e
  disjoint D e
  disjoint F e
  disjoint N e
  disjoint A f
  disjoint A g
  disjoint e f
  disjoint e g
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint C f
  disjoint C g
  disjoint D f
  disjoint D g
  disjoint F f
  disjoint F g
  disjoint N f
  disjoint N g
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , C >. /\ <. A , C >. Cgr <. D , F >. ) -> E. e e. ( EE ` N ) ( e Btwn <. D , F >. /\ <. A , <. B , C >. >. Cgr3 <. D , <. e , F >. >. ) ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    #
    cD
    @1
    wcel
    #
    cF
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cB
    cA
    cC
    cop
    #
    cbtwn
    wbr
    #
    @10
    cD
    cF
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    ve
    cv
    #
    @12
    cbtwn
    wbr
    #
    cA
    cB
    cC
    cop
    #
    cop
    cD
    @15
    cF
    cop
    #
    cop
    ccgr3
    wbr
    #
    wa
    #
    ve
    @1
    wrex
    #
    @9
    @14
    wa
    #
    cD
    cF
    vg
    cv
    #
    cop
    cbtwn
    wbr
    #
    cD
    @23
    wne
    #
    wa
    #
    vg
    @1
    wrex
    #
    @21
    @22
    @0
    @7
    @6
    @27
    @0
    @5
    @8
    @14
    simpl1
    @6
    @7
    @0
    @5
    @14
    simpl3r
    @6
    @7
    @0
    @5
    @14
    simpl3l
    cF
    cD
    cN
    vg
    btwndiff
    syl3anc
    @22
    @26
    @21
    vg
    @1
    @9
    @23
    @1
    wcel
    #
    @14
    @26
    @21
    wi
    @9
    @28
    wa
    #
    @14
    @26
    @21
    @29
    @14
    @26
    wa
    #
    wa
    #
    cD
    @23
    @15
    cop
    cbtwn
    wbr
    #
    cD
    @15
    cop
    #
    cA
    cB
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    ve
    @1
    wrex
    #
    @21
    @29
    @37
    @30
    @29
    @0
    @28
    @6
    @2
    @3
    @37
    @0
    @5
    @8
    @28
    simpl1
    @9
    @28
    simpr
    @6
    @7
    @0
    @5
    @28
    simpl3l
    @2
    @3
    @4
    @0
    @8
    @28
    simpl21
    @2
    @3
    @4
    @0
    @8
    @28
    simpl22
    ve
    @23
    cD
    cA
    cB
    cN
    axsegcon
    syl122anc
    adantr
    @31
    @36
    @20
    ve
    @1
    @29
    @15
    @1
    wcel
    #
    @30
    @36
    @20
    wi
    #
    @29
    @38
    wa
    @9
    @28
    @38
    wa
    #
    wa
    #
    @30
    @39
    @9
    @28
    @38
    anass
    @41
    @30
    @36
    @20
    @41
    @30
    @36
    wa
    #
    wa
    #
    @15
    @23
    vf
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @15
    @44
    cop
    #
    @17
    ccgr
    wbr
    #
    wa
    #
    vf
    @1
    wrex
    #
    @20
    @41
    @50
    @42
    @41
    @0
    @28
    @38
    @3
    @4
    @50
    @0
    @5
    @8
    @40
    simpl1
    @9
    @28
    @38
    simprl
    @9
    @28
    @38
    simprr
    @2
    @3
    @4
    @0
    @8
    @40
    simpl22
    @2
    @3
    @4
    @0
    @8
    @40
    simpl23
    vf
    @23
    @15
    cB
    cC
    cN
    axsegcon
    syl122anc
    adantr
    @43
    @49
    @20
    vf
    @1
    @41
    @44
    @1
    wcel
    #
    @42
    @49
    @20
    wi
    #
    @41
    @51
    wa
    #
    @9
    @28
    @38
    @51
    w3a
    #
    wa
    #
    @42
    @52
    @53
    @9
    @40
    @51
    wa
    #
    wa
    @55
    @9
    @40
    @51
    anass
    @54
    @56
    @9
    @28
    @38
    @51
    df-3an
    anbi2i
    bitr4i
    @55
    @42
    @49
    @20
    @55
    @42
    @49
    wa
    #
    wa
    #
    @44
    cF
    wceq
    #
    @20
    @55
    @57
    @59
    @55
    @57
    @23
    cD
    wne
    #
    cD
    @45
    cbtwn
    wbr
    #
    cD
    @44
    cop
    @10
    ccgr
    wbr
    #
    wa
    #
    cD
    @23
    cF
    cop
    #
    cbtwn
    wbr
    #
    @12
    @10
    ccgr
    wbr
    #
    wa
    #
    w3a
    #
    @59
    @55
    @57
    @68
    @58
    @60
    @63
    @67
    @58
    cD
    @23
    @42
    @25
    @55
    @49
    @14
    @24
    @25
    @36
    simplrr
    ad2antrl
    necomd
    @58
    @61
    @62
    @55
    @57
    @23
    cD
    @15
    @44
    cN
    @0
    @5
    @8
    @54
    simpl1
    #
    @9
    @28
    @38
    @51
    simpr1
    #
    @6
    @7
    @0
    @5
    @54
    simpl3l
    #
    @9
    @28
    @38
    @51
    simpr2
    #
    @9
    @28
    @38
    @51
    simpr3
    #
    @42
    @32
    @55
    @49
    @30
    @32
    @35
    simprl
    #
    ad2antrl
    #
    @55
    @42
    @46
    @48
    simprrl
    #
    btwnexchand
    @55
    @57
    cD
    @15
    @44
    cA
    cB
    cC
    cN
    @69
    @71
    @72
    @73
    @2
    @3
    @4
    @0
    @8
    @54
    simpl21
    #
    @2
    @3
    @4
    @0
    @8
    @54
    simpl22
    #
    @2
    @3
    @4
    @0
    @8
    @54
    simpl23
    #
    @55
    @57
    @23
    cD
    @15
    @44
    cN
    @69
    @70
    @71
    @72
    @73
    @75
    @76
    btwnexch3and
    @42
    @11
    @55
    @49
    @11
    @13
    @26
    @36
    simplll
    ad2antrl
    @42
    @35
    @55
    @49
    @30
    @32
    @35
    simprr
    ad2antrl
    @55
    @42
    @46
    @48
    simprrr
    cgrextendand
    jca
    @58
    @65
    @66
    @55
    @57
    cD
    cF
    @23
    cN
    @69
    @71
    @6
    @7
    @0
    @5
    @54
    simpl3r
    #
    @70
    @42
    @24
    @55
    @49
    @14
    @24
    @25
    @36
    simplrl
    ad2antrl
    btwncomand
    @55
    @57
    cA
    cC
    cD
    cF
    cN
    @69
    @77
    @79
    @71
    @80
    @42
    @13
    @55
    @49
    @11
    @13
    @26
    @36
    simpllr
    #
    ad2antrl
    cgrcomand
    jca
    3jca
    ex
    @55
    @0
    @6
    @2
    @4
    @28
    @51
    @7
    @68
    @59
    wi
    @69
    @71
    @77
    @79
    @70
    @73
    @80
    cD
    cA
    cC
    @23
    cN
    @44
    cF
    segconeq
    syl133anc
    syld
    imp
    @55
    @42
    @49
    @59
    @20
    wi
    @55
    @42
    wa
    #
    @59
    @49
    @20
    @59
    @49
    wa
    @15
    @64
    cbtwn
    wbr
    #
    @18
    @17
    ccgr
    wbr
    #
    wa
    #
    @82
    @20
    @59
    @49
    @85
    @59
    @46
    @83
    @48
    @84
    @59
    @45
    @64
    @15
    cbtwn
    @44
    cF
    @23
    opeq2
    breq2d
    @59
    @47
    @18
    @17
    ccgr
    @44
    cF
    @15
    opeq2
    breq1d
    anbi12d
    biimpa
    @55
    @42
    @85
    @20
    @55
    @42
    @85
    wa
    #
    wa
    #
    @16
    @19
    @55
    @86
    @16
    @42
    @55
    @32
    @83
    @16
    @85
    @74
    @83
    @84
    simpl
    @55
    @0
    @28
    @6
    @38
    @7
    @32
    @83
    wa
    @16
    wi
    @69
    @70
    @71
    @72
    @80
    @23
    cD
    @15
    cF
    cN
    btwnexch3
    syl122anc
    syl2ani
    imp
    @87
    @19
    @34
    @33
    ccgr
    wbr
    #
    @13
    @17
    @18
    ccgr
    wbr
    #
    @55
    @86
    cD
    @15
    cA
    cB
    cN
    @69
    @71
    @72
    @77
    @78
    @86
    @35
    @55
    @30
    @32
    @35
    @85
    simplrr
    adantl
    cgrcomand
    @42
    @13
    @55
    @85
    @81
    ad2antrl
    @55
    @86
    @15
    cF
    cB
    cC
    cN
    @69
    @72
    @80
    @78
    @79
    @55
    @42
    @83
    @84
    simprrr
    cgrcomand
    @55
    @19
    @88
    @13
    @89
    w3a
    wb
    #
    @86
    @55
    @0
    @2
    @3
    @4
    @6
    @38
    @7
    @90
    @69
    @77
    @78
    @79
    @71
    @72
    @80
    cA
    cB
    cC
    cD
    @15
    cF
    cN
    brcgr3
    syl133anc
    adantr
    mpbir3and
    jca
    expr
    syl5
    expcomd
    impr
    mpd
    expr
    sylanb
    an32s
    rexlimdva
    mpd
    expr
    sylanb
    an32s
    reximdva
    mpd
    expr
    an32s
    rexlimdva
    mpd
    ex
end
