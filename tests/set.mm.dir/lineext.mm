include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "cop.mm"
include "ccolin.mm"
include "wbr.mm"
include "ccgr.mm"
include "cbtwn.mm"
include "w3o.mm"
include "cv.mm"
include "ccgr3.mm"
include "wrex.mm"
include "wb.mm"
include "brcolinear.mm"
include "3adant3.mm"
include "anbi1d.mm"
include "wi.mm"
include "simp1.mm"
include "simp3r.mm"
include "simp3l.mm"
include "jca.mm"
include "simp21.mm"
include "simp23.mm"
include "3jca.mm"
include "adantr.mm"
include "axsegcon.mm"
include "syl.mm"
include "simprlr.mm"
include "simprrr.mm"
include "an4.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "cgrcomlr.mm"
include "syl122anc.mm"
include "anbi2d.mm"
include "simpl23.mm"
include "simpr.mm"
include "cgrextend.mm"
include "syl133anc.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "imp.mm"
include "expr.mm"
include "cgrcom.mm"
include "simpl2.mm"
include "brcgr3.mm"
include "syl113anc.mm"
include "3imtr4d.mm"
include "an32s.mm"
include "reximdva.mm"
include "mpd.mm"
include "exp32.mm"
include "3ancoma.mm"
include "btwncom.mm"
include "sylan2b.mm"
include "simp3.mm"
include "simp22.mm"
include "syl112anc.mm"
include "simpll.mm"
include "simplr.mm"
include "ex.mm"
include "adantl.mm"
include "sylcom.mm"
include "syl5bb.mm"
include "expdimp.mm"
include "sylbird.mm"
include "cgrxfr.mm"
include "syl131anc.mm"
include "cgr3permute1.mm"
include "biimprd.mm"
include "adantld.mm"
include "syld.mm"
include "expd.mm"
include "3jaod.mm"
include "impd.mm"

theorem lineext
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let cE: class E
  let cN: class N

  disjoint N f
  disjoint A f
  disjoint B f
  disjoint C f
  disjoint D f
  disjoint E f
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) ) ) -> ( ( A Colinear <. B , C >. /\ <. A , B >. Cgr <. D , E >. ) -> E. f e. ( EE ` N ) <. A , <. B , C >. >. Cgr3 <. D , <. E , f >. >. ) )

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
    cE
    @1
    wcel
    #
    wa
    #
    w3a
    #
    cA
    cB
    cC
    cop
    #
    ccolin
    wbr
    #
    cA
    cB
    cop
    #
    cD
    cE
    cop
    #
    ccgr
    wbr
    #
    wa
    cA
    @10
    cbtwn
    wbr
    #
    cB
    cC
    cA
    cop
    cbtwn
    wbr
    #
    cC
    @12
    cbtwn
    wbr
    #
    w3o
    #
    @14
    wa
    cA
    @10
    cop
    cD
    cE
    vf
    cv
    #
    cop
    #
    cop
    ccgr3
    wbr
    #
    vf
    @1
    wrex
    #
    @9
    @11
    @18
    @14
    @0
    @5
    @11
    @18
    wb
    @8
    cA
    cB
    cC
    cN
    brcolinear
    3adant3
    anbi1d
    @9
    @18
    @14
    @22
    @9
    @15
    @14
    @22
    wi
    #
    @16
    @17
    @9
    @15
    @14
    @22
    @9
    @15
    @14
    wa
    #
    wa
    #
    cD
    @20
    cbtwn
    wbr
    #
    cD
    @19
    cop
    #
    cA
    cC
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vf
    @1
    wrex
    #
    @22
    @25
    @0
    @7
    @6
    wa
    #
    @2
    @4
    wa
    #
    w3a
    #
    @31
    @9
    @34
    @24
    @9
    @0
    @32
    @33
    @0
    @5
    @8
    simp1
    #
    @9
    @7
    @6
    @0
    @5
    @6
    @7
    simp3r
    @0
    @5
    @6
    @7
    simp3l
    jca
    @9
    @2
    @4
    @0
    @2
    @3
    @4
    @8
    simp21
    #
    @0
    @2
    @3
    @4
    @8
    simp23
    #
    jca
    3jca
    adantr
    vf
    cE
    cD
    cA
    cC
    cN
    axsegcon
    syl
    @25
    @30
    @21
    vf
    @1
    @9
    @19
    @1
    wcel
    #
    @24
    @30
    @21
    wi
    @9
    @38
    wa
    #
    @24
    wa
    @26
    @28
    @27
    ccgr
    wbr
    #
    wa
    #
    @14
    @40
    @10
    @20
    ccgr
    wbr
    #
    w3a
    #
    @30
    @21
    @39
    @24
    @41
    @43
    @39
    @24
    @41
    wa
    #
    wa
    @14
    @40
    @42
    @39
    @15
    @14
    @41
    simprlr
    @39
    @24
    @26
    @40
    simprrr
    @39
    @44
    @42
    @44
    @15
    @26
    wa
    #
    @14
    @40
    wa
    #
    wa
    #
    @39
    @42
    @15
    @14
    @26
    @40
    an4
    @39
    @47
    @45
    cB
    cA
    cop
    cE
    cD
    cop
    ccgr
    wbr
    #
    @40
    wa
    #
    wa
    #
    @42
    @39
    @46
    @49
    @45
    @39
    @14
    @48
    @40
    @39
    @0
    @2
    @3
    @6
    @7
    @14
    @48
    wb
    @0
    @5
    @8
    @38
    simpl1
    #
    @2
    @3
    @4
    @0
    @8
    @38
    simpl21
    #
    @2
    @3
    @4
    @0
    @8
    @38
    simpl22
    #
    @6
    @7
    @0
    @5
    @38
    simpl3l
    #
    @6
    @7
    @0
    @5
    @38
    simpl3r
    #
    cA
    cB
    cD
    cE
    cN
    cgrcomlr
    syl122anc
    anbi1d
    anbi2d
    @39
    @0
    @3
    @2
    @4
    @7
    @6
    @38
    @50
    @42
    wi
    @51
    @53
    @52
    @2
    @3
    @4
    @0
    @8
    @38
    simpl23
    #
    @55
    @54
    @9
    @38
    simpr
    #
    cB
    cA
    cC
    cE
    cD
    @19
    cN
    cgrextend
    syl133anc
    sylbid
    syl5bi
    imp
    3jca
    expr
    @39
    @30
    @41
    wb
    @24
    @39
    @29
    @40
    @26
    @39
    @0
    @6
    @38
    @2
    @4
    @29
    @40
    wb
    @51
    @54
    @57
    @52
    @56
    cD
    @19
    cA
    cC
    cN
    cgrcom
    syl122anc
    anbi2d
    adantr
    @39
    @21
    @43
    wb
    #
    @24
    @39
    @0
    @5
    @6
    @7
    @38
    @58
    @51
    @0
    @5
    @8
    @38
    simpl2
    #
    @54
    @55
    @57
    cA
    cB
    cC
    cD
    cE
    @19
    cN
    brcgr3
    syl113anc
    #
    adantr
    3imtr4d
    an32s
    reximdva
    mpd
    exp32
    @9
    @16
    cB
    @28
    cbtwn
    wbr
    #
    @23
    @0
    @5
    @61
    @16
    wb
    #
    @8
    @5
    @0
    @3
    @2
    @4
    w3a
    @62
    @2
    @3
    @4
    3ancoma
    cB
    cA
    cC
    cN
    btwncom
    sylan2b
    3adant3
    @9
    @61
    @14
    @22
    @9
    @61
    @14
    wa
    #
    wa
    #
    cE
    @27
    cbtwn
    wbr
    #
    @20
    @10
    ccgr
    wbr
    #
    wa
    #
    vf
    @1
    wrex
    #
    @22
    @9
    @68
    @63
    @9
    @0
    @8
    @3
    @4
    @68
    @35
    @0
    @5
    @8
    simp3
    #
    @0
    @2
    @3
    @4
    @8
    simp22
    #
    @37
    vf
    cD
    cE
    cB
    cC
    cN
    axsegcon
    syl112anc
    adantr
    @64
    @67
    @21
    vf
    @1
    @9
    @38
    @63
    @67
    @21
    wi
    @39
    @63
    @67
    @21
    @39
    @61
    @65
    wa
    #
    @14
    @42
    wa
    #
    wa
    #
    @43
    @63
    @67
    wa
    #
    @21
    @39
    @73
    @40
    @43
    @39
    @0
    @5
    @6
    @7
    @38
    @73
    @40
    wi
    @51
    @59
    @54
    @55
    @57
    cA
    cB
    cC
    cD
    cE
    @19
    cN
    cgrextend
    syl113anc
    @72
    @40
    @43
    wi
    @71
    @72
    @40
    @43
    @72
    @40
    wa
    @14
    @40
    @42
    @14
    @42
    @40
    simpll
    @72
    @40
    simpr
    @14
    @42
    @40
    simplr
    3jca
    ex
    adantl
    sylcom
    @74
    @71
    @14
    @66
    wa
    #
    wa
    @39
    @73
    @61
    @14
    @65
    @66
    an4
    @39
    @75
    @72
    @71
    @39
    @66
    @42
    @14
    @39
    @0
    @7
    @38
    @3
    @4
    @66
    @42
    wb
    @51
    @55
    @57
    @53
    @56
    cE
    @19
    cB
    cC
    cN
    cgrcom
    syl122anc
    anbi2d
    anbi2d
    syl5bb
    @60
    3imtr4d
    expdimp
    an32s
    reximdva
    mpd
    exp32
    sylbird
    @9
    @17
    @14
    @22
    @9
    @17
    @14
    wa
    #
    @19
    @13
    cbtwn
    wbr
    #
    cA
    cC
    cB
    cop
    cop
    cD
    @19
    cE
    cop
    cop
    ccgr3
    wbr
    #
    wa
    #
    vf
    @1
    wrex
    #
    @22
    @9
    @0
    @2
    @4
    @3
    @8
    @76
    @80
    wi
    @35
    @36
    @37
    @70
    @69
    cA
    cC
    cB
    cD
    vf
    cE
    cN
    cgrxfr
    syl131anc
    @9
    @79
    @21
    vf
    @1
    @39
    @78
    @21
    @77
    @39
    @21
    @78
    @39
    @0
    @5
    @6
    @7
    @38
    @21
    @78
    wb
    @51
    @59
    @54
    @55
    @57
    cA
    cB
    cC
    cD
    cE
    @19
    cN
    cgr3permute1
    syl113anc
    biimprd
    adantld
    reximdva
    syld
    expd
    3jaod
    impd
    sylbid
end
