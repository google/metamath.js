include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "simpl1.mm"
include "simpl23.mm"
include "simpl21.mm"
include "simpl31.mm"
include "3jca.mm"
include "simpl32.mm"
include "simpl33.mm"
include "jca.mm"
include "simpr2.mm"
include "wb.mm"
include "btwncom.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "simpr3.mm"
include "axpasch.mm"
include "sylc.mm"
include "simp1l1.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simpl22.mm"
include "simp3l.mm"
include "simp1r1.mm"
include "simpll1.mm"
include "syl.mm"
include "simpll2.mm"
include "simplr.mm"
include "simpl3r.mm"
include "anim1i.mm"
include "btwnexch2.mm"
include "ex.mm"
include "anim1d.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexlimdv3a.mm"

theorem trisegint
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cE: class E
  let cN: class N
  let vq: setvar q
  let vr: setvar r

  disjoint A q
  disjoint B q
  disjoint C q
  disjoint D q
  disjoint E q
  disjoint N q
  disjoint P q
  disjoint A r
  disjoint q r
  disjoint B r
  disjoint C r
  disjoint D r
  disjoint E r
  disjoint N r
  disjoint P r
  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ P e. ( EE ` N ) ) ) -> ( ( B Btwn <. A , C >. /\ E Btwn <. D , C >. /\ P Btwn <. A , D >. ) -> E. q e. ( EE ` N ) ( q Btwn <. P , C >. /\ q Btwn <. B , E >. ) ) )

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
    cP
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
    cbtwn
    wbr
    #
    cE
    cD
    cC
    cop
    cbtwn
    wbr
    #
    cP
    cA
    cD
    cop
    cbtwn
    wbr
    #
    w3a
    #
    vq
    cv
    #
    cP
    cC
    cop
    #
    cbtwn
    wbr
    #
    @15
    cB
    cE
    cop
    cbtwn
    wbr
    #
    wa
    #
    vq
    @1
    wrex
    #
    @10
    @14
    wa
    #
    vr
    cv
    #
    cE
    cA
    cop
    cbtwn
    wbr
    #
    @22
    @16
    cbtwn
    wbr
    #
    wa
    #
    vr
    @1
    wrex
    #
    @20
    @21
    @0
    @4
    @2
    @6
    w3a
    #
    @7
    @8
    wa
    #
    w3a
    cE
    cC
    cD
    cop
    cbtwn
    wbr
    #
    @13
    wa
    @26
    @21
    @0
    @27
    @28
    @0
    @5
    @9
    @14
    simpl1
    #
    @21
    @4
    @2
    @6
    @2
    @3
    @4
    @0
    @9
    @14
    simpl23
    #
    @2
    @3
    @4
    @0
    @9
    @14
    simpl21
    #
    @6
    @7
    @8
    @0
    @5
    @14
    simpl31
    #
    3jca
    @21
    @7
    @8
    @6
    @7
    @8
    @0
    @5
    @14
    simpl32
    #
    @6
    @7
    @8
    @0
    @5
    @14
    simpl33
    #
    jca
    3jca
    @21
    @29
    @13
    @21
    @12
    @29
    @10
    @11
    @12
    @13
    simpr2
    @21
    @0
    @7
    @6
    @4
    @12
    @29
    wb
    @30
    @34
    @33
    @31
    cE
    cD
    cC
    cN
    btwncom
    syl13anc
    mpbid
    @10
    @11
    @12
    @13
    simpr3
    jca
    vr
    cC
    cA
    cD
    cE
    cP
    cN
    axpasch
    sylc
    @21
    @25
    @20
    vr
    @1
    @21
    @22
    @1
    wcel
    #
    @25
    w3a
    #
    @15
    @22
    cC
    cop
    cbtwn
    wbr
    #
    @18
    wa
    #
    vq
    @1
    wrex
    #
    @20
    @37
    @0
    @7
    @4
    @2
    w3a
    #
    @36
    @3
    wa
    #
    w3a
    @23
    cB
    cC
    cA
    cop
    cbtwn
    wbr
    #
    wa
    @40
    @37
    @0
    @41
    @42
    @0
    @5
    @9
    @14
    @36
    @25
    simp1l1
    #
    @37
    @7
    @4
    @2
    @21
    @36
    @7
    @25
    @34
    3ad2ant1
    @21
    @36
    @4
    @25
    @31
    3ad2ant1
    #
    @21
    @36
    @2
    @25
    @32
    3ad2ant1
    #
    3jca
    @37
    @36
    @3
    @21
    @36
    @25
    simp2
    @21
    @36
    @3
    @25
    @2
    @3
    @4
    @0
    @9
    @14
    simpl22
    3ad2ant1
    #
    jca
    3jca
    @37
    @23
    @43
    @21
    @36
    @23
    @24
    simp3l
    @37
    @11
    @43
    @11
    @12
    @13
    @10
    @36
    @25
    simp1r1
    @37
    @0
    @3
    @2
    @4
    @11
    @43
    wb
    @44
    @47
    @46
    @45
    cB
    cA
    cC
    cN
    btwncom
    syl13anc
    mpbid
    jca
    vq
    cE
    cC
    cA
    @22
    cB
    cN
    axpasch
    sylc
    @37
    @39
    @19
    vq
    @1
    @37
    @15
    @1
    wcel
    #
    wa
    #
    @38
    @17
    @18
    @49
    @38
    @17
    @49
    @38
    wa
    #
    @0
    @8
    @36
    wa
    #
    @48
    @4
    wa
    #
    w3a
    @24
    @38
    wa
    @17
    @50
    @0
    @51
    @52
    @50
    @21
    @0
    @21
    @36
    @25
    @48
    @38
    simpll1
    #
    @30
    syl
    @50
    @8
    @36
    @50
    @21
    @8
    @53
    @35
    syl
    @21
    @36
    @25
    @48
    @38
    simpll2
    jca
    @50
    @48
    @4
    @37
    @48
    @38
    simplr
    @50
    @21
    @4
    @53
    @31
    syl
    jca
    3jca
    @49
    @24
    @38
    @23
    @24
    @21
    @36
    @48
    simpl3r
    anim1i
    cP
    @22
    @15
    cC
    cN
    btwnexch2
    sylc
    ex
    anim1d
    reximdva
    mpd
    rexlimdv3a
    mpd
    ex
end
