include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr3.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "ccgr.mm"
include "brcgr3.mm"
include "simp2.mm"
include "syl6bi.mm"
include "wi.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31.mm"
include "simp33.mm"
include "cgrxfr.mm"
include "syl132anc.mm"
include "sylan2d.mm"
include "imp.mm"
include "wceq.mm"
include "simprrl.mm"
include "jca.mm"
include "simpl1.mm"
include "simpl31.mm"
include "simpl33.mm"
include "cgrrflxd.mm"
include "simpr.mm"
include "adantr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "3jca.mm"
include "cgr3tr4.mm"
include "syl13anc.mm"
include "wb.mm"
include "cgr3com.mm"
include "syl113anc.mm"
include "simpl32.mm"
include "syl133anc.mm"
include "simpr1.mm"
include "simpr3.mm"
include "cgrcomlrand.mm"
include "ex.mm"
include "sylbid.mm"
include "syld.mm"
include "syl2ani.mm"
include "cifs.mm"
include "brifs.mm"
include "ifscgr.mm"
include "sylbird.mm"
include "syl333anc.mm"
include "cgrid2.mm"
include "eqbrtrrd.mm"
include "expr.mm"
include "an32s.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem btwnxfr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  let ve: setvar e


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , C >. /\ <. A , <. B , C >. >. Cgr3 <. D , <. E , F >. >. ) -> E Btwn <. D , F >. ) )

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
    cF
    @1
    wcel
    #
    w3a
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
    cA
    cB
    cC
    cop
    #
    cop
    #
    cD
    cE
    cF
    cop
    #
    cop
    #
    ccgr3
    wbr
    #
    wa
    #
    cE
    cD
    cF
    cop
    #
    cbtwn
    wbr
    #
    @10
    @18
    wa
    #
    ve
    cv
    #
    @19
    cbtwn
    wbr
    #
    @14
    cD
    @22
    cF
    cop
    #
    cop
    #
    ccgr3
    wbr
    #
    wa
    #
    ve
    @1
    wrex
    #
    @20
    @10
    @18
    @28
    @10
    @17
    @11
    @19
    ccgr
    wbr
    #
    @12
    @28
    @10
    @17
    cA
    cB
    cop
    cD
    cE
    cop
    #
    ccgr
    wbr
    #
    @29
    @13
    @15
    ccgr
    wbr
    #
    w3a
    @29
    cA
    cB
    cC
    cD
    cE
    cF
    cN
    brcgr3
    @31
    @29
    @32
    simp2
    syl6bi
    @10
    @0
    @2
    @3
    @4
    @6
    @8
    @12
    @29
    wa
    @28
    wi
    @0
    @5
    @9
    simp1
    @0
    @2
    @3
    @4
    @9
    simp21
    @0
    @2
    @3
    @4
    @9
    simp22
    @0
    @2
    @3
    @4
    @9
    simp23
    @0
    @5
    @6
    @7
    @8
    simp31
    @0
    @5
    @6
    @7
    @8
    simp33
    cA
    cB
    cC
    cD
    ve
    cF
    cN
    cgrxfr
    syl132anc
    sylan2d
    imp
    @21
    @27
    @20
    ve
    @1
    @10
    @22
    @1
    wcel
    #
    @18
    @27
    @20
    wi
    @10
    @33
    wa
    #
    @18
    @27
    @20
    @34
    @18
    @27
    wa
    #
    wa
    #
    @22
    cE
    @19
    cbtwn
    @34
    @35
    @22
    cE
    wceq
    #
    @34
    @35
    @22
    @22
    cop
    @22
    cE
    cop
    ccgr
    wbr
    #
    @37
    @34
    @35
    @23
    @23
    wa
    #
    @19
    @19
    ccgr
    wbr
    #
    @24
    @24
    ccgr
    wbr
    #
    wa
    #
    cD
    @22
    cop
    #
    @30
    ccgr
    wbr
    #
    cF
    @22
    cop
    #
    cF
    cE
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    w3a
    #
    @38
    @34
    @35
    @49
    @36
    @39
    @42
    @48
    @36
    @23
    @23
    @34
    @18
    @23
    @26
    simprrl
    #
    @50
    jca
    @34
    @42
    @35
    @34
    @40
    @41
    @34
    cD
    cF
    cN
    @0
    @5
    @9
    @33
    simpl1
    #
    @6
    @7
    @8
    @0
    @5
    @33
    simpl31
    #
    @6
    @7
    @8
    @0
    @5
    @33
    simpl33
    #
    cgrrflxd
    @34
    @22
    cF
    cN
    @51
    @10
    @33
    simpr
    #
    @53
    cgrrflxd
    jca
    adantr
    @34
    @35
    @48
    @18
    @34
    @17
    @26
    @48
    @27
    @12
    @17
    simpr
    @23
    @26
    simpr
    @34
    @17
    @26
    wa
    #
    @16
    @25
    ccgr3
    wbr
    #
    @48
    @34
    @0
    @5
    @9
    @6
    @33
    @8
    w3a
    @55
    @56
    wi
    @51
    @0
    @5
    @9
    @33
    simpl2
    @0
    @5
    @9
    @33
    simpl3
    #
    @34
    @6
    @33
    @8
    @52
    @54
    @53
    3jca
    cA
    cB
    cC
    cD
    cE
    cF
    cD
    @22
    cF
    cN
    cgr3tr4
    syl13anc
    @34
    @56
    @25
    @16
    ccgr3
    wbr
    #
    @48
    @34
    @0
    @9
    @6
    @33
    @8
    @56
    @58
    wb
    @51
    @57
    @52
    @54
    @53
    cD
    cE
    cF
    cD
    @22
    cF
    cN
    cgr3com
    syl113anc
    @34
    @58
    @44
    @40
    @24
    @15
    ccgr
    wbr
    #
    w3a
    #
    @48
    @34
    @0
    @6
    @33
    @8
    @6
    @7
    @8
    @58
    @60
    wb
    @51
    @52
    @54
    @53
    @52
    @6
    @7
    @8
    @0
    @5
    @33
    simpl32
    #
    @53
    cD
    @22
    cF
    cD
    cE
    cF
    cN
    brcgr3
    syl133anc
    @34
    @60
    @48
    @34
    @60
    wa
    @44
    @47
    @34
    @44
    @40
    @59
    simpr1
    @34
    @60
    @22
    cF
    cE
    cF
    cN
    @51
    @54
    @53
    @61
    @53
    @34
    @44
    @40
    @59
    simpr3
    cgrcomlrand
    jca
    ex
    sylbid
    sylbid
    syld
    syl2ani
    imp
    3jca
    ex
    @34
    @0
    @6
    @33
    @8
    @33
    @6
    @33
    @8
    @7
    @49
    @38
    wi
    @51
    @52
    @54
    @53
    @54
    @52
    @54
    @53
    @61
    @0
    @6
    @33
    w3a
    @8
    @33
    @6
    w3a
    @33
    @8
    @7
    w3a
    w3a
    @49
    @43
    @45
    cop
    @43
    @46
    cop
    cifs
    wbr
    @38
    cD
    @22
    cF
    @22
    cD
    @22
    cF
    cE
    cN
    brifs
    cD
    @22
    cF
    @22
    cD
    @22
    cF
    cE
    cN
    ifscgr
    sylbird
    syl333anc
    syld
    @34
    @0
    @33
    @33
    @7
    @38
    @37
    wi
    @51
    @54
    @54
    @61
    @22
    @22
    cE
    cN
    cgrid2
    syl13anc
    syld
    imp
    @50
    eqbrtrrd
    expr
    an32s
    rexlimdva
    mpd
    ex
end
