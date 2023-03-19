include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cop.mm"
include "ccgr.mm"
include "wbr.mm"
include "csegle.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "cbtwn.mm"
include "wrex.mm"
include "ccgr3.mm"
include "simprrl.mm"
include "simprlr.mm"
include "simpl11.mm"
include "simpl21.mm"
include "simpr.mm"
include "simpl22.mm"
include "simpl32.mm"
include "simpl33.mm"
include "cgrxfr.mm"
include "syl132anc.mm"
include "adantr.mm"
include "mp2and.mm"
include "anass.mm"
include "wb.mm"
include "simprl.mm"
include "simprr.mm"
include "brcgr3.mm"
include "syl133anc.mm"
include "df-3an.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpr1l.mm"
include "simpr2r.mm"
include "cgrtr4and.mm"
include "simpr31.mm"
include "cgrtrand.mm"
include "sylan2br.mm"
include "expr.mm"
include "sylbid.mm"
include "anim2d.mm"
include "sylanb.mm"
include "an32s.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexlimdva.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp22.mm"
include "brsegle.mm"
include "syl122anc.mm"
include "simp23.mm"
include "simp31.mm"
include "simp32.mm"
include "simp33.mm"
include "3imtr4d.mm"
include "exp32.mm"
include "3impd.mm"

theorem seglecgr12im
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( ( N e. NN /\ A e. ( EE ` N ) /\ B e. ( EE ` N ) ) /\ ( C e. ( EE ` N ) /\ D e. ( EE ` N ) /\ E e. ( EE ` N ) ) /\ ( F e. ( EE ` N ) /\ G e. ( EE ` N ) /\ H e. ( EE ` N ) ) ) -> ( ( <. A , B >. Cgr <. E , F >. /\ <. C , D >. Cgr <. G , H >. /\ <. A , B >. Seg<_ <. C , D >. ) -> <. E , F >. Seg<_ <. G , H >. ) )

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
    w3a
    #
    cC
    @1
    wcel
    #
    cD
    @1
    wcel
    #
    cE
    @1
    wcel
    #
    w3a
    #
    cF
    @1
    wcel
    #
    cG
    @1
    wcel
    #
    cH
    @1
    wcel
    #
    w3a
    #
    w3a
    #
    cA
    cB
    cop
    #
    cE
    cF
    cop
    #
    ccgr
    wbr
    #
    cC
    cD
    cop
    #
    cG
    cH
    cop
    #
    ccgr
    wbr
    #
    @14
    @17
    csegle
    wbr
    #
    @15
    @18
    csegle
    wbr
    #
    @13
    @16
    @19
    @20
    @21
    wi
    @13
    @16
    @19
    wa
    #
    wa
    #
    vy
    cv
    #
    @17
    cbtwn
    wbr
    #
    @14
    cC
    @24
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vy
    @1
    wrex
    #
    vz
    cv
    #
    @18
    cbtwn
    wbr
    #
    @15
    cG
    @30
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vz
    @1
    wrex
    #
    @20
    @21
    @23
    @28
    @35
    vy
    @1
    @13
    @24
    @1
    wcel
    #
    @22
    @28
    @35
    wi
    @13
    @36
    wa
    #
    @22
    @28
    @35
    @37
    @22
    @28
    wa
    #
    wa
    #
    @31
    cC
    @24
    cD
    cop
    #
    cop
    cG
    @30
    cH
    cop
    #
    cop
    ccgr3
    wbr
    #
    wa
    #
    vz
    @1
    wrex
    #
    @35
    @39
    @25
    @19
    @44
    @37
    @22
    @25
    @27
    simprrl
    @37
    @16
    @19
    @28
    simprlr
    @37
    @25
    @19
    wa
    @44
    wi
    #
    @38
    @37
    @0
    @5
    @36
    @6
    @10
    @11
    @45
    @0
    @2
    @3
    @8
    @12
    @36
    simpl11
    @5
    @6
    @7
    @4
    @12
    @36
    simpl21
    @13
    @36
    simpr
    @5
    @6
    @7
    @4
    @12
    @36
    simpl22
    @9
    @10
    @11
    @4
    @8
    @36
    simpl32
    @9
    @10
    @11
    @4
    @8
    @36
    simpl33
    cC
    @24
    cD
    cG
    vz
    cH
    cN
    cgrxfr
    syl132anc
    adantr
    mp2and
    @39
    @43
    @34
    vz
    @1
    @37
    @30
    @1
    wcel
    #
    @38
    @43
    @34
    wi
    #
    @37
    @46
    wa
    @13
    @36
    @46
    wa
    #
    wa
    #
    @38
    @47
    @13
    @36
    @46
    anass
    @49
    @38
    wa
    #
    @42
    @33
    @31
    @50
    @42
    @26
    @32
    ccgr
    wbr
    #
    @19
    @40
    @41
    ccgr
    wbr
    #
    w3a
    #
    @33
    @49
    @42
    @53
    wb
    #
    @38
    @49
    @0
    @5
    @36
    @6
    @10
    @46
    @11
    @54
    @0
    @2
    @3
    @8
    @12
    @48
    simpl11
    #
    @5
    @6
    @7
    @4
    @12
    @48
    simpl21
    #
    @13
    @36
    @46
    simprl
    #
    @5
    @6
    @7
    @4
    @12
    @48
    simpl22
    @9
    @10
    @11
    @4
    @8
    @48
    simpl32
    #
    @13
    @36
    @46
    simprr
    #
    @9
    @10
    @11
    @4
    @8
    @48
    simpl33
    cC
    @24
    cD
    cG
    @30
    cH
    cN
    brcgr3
    syl133anc
    adantr
    @49
    @38
    @53
    @33
    @38
    @53
    wa
    @49
    @22
    @28
    @53
    w3a
    #
    @33
    @22
    @28
    @53
    df-3an
    @49
    @60
    cE
    cF
    cC
    @24
    cG
    @30
    cN
    @55
    @5
    @6
    @7
    @4
    @12
    @48
    simpl23
    #
    @9
    @10
    @11
    @4
    @8
    @48
    simpl31
    #
    @56
    @57
    @58
    @59
    @49
    @60
    cA
    cB
    cE
    cF
    cC
    @24
    cN
    @55
    @0
    @2
    @3
    @8
    @12
    @48
    simpl12
    @0
    @2
    @3
    @8
    @12
    @48
    simpl13
    @61
    @62
    @56
    @57
    @16
    @19
    @28
    @53
    @49
    simpr1l
    @25
    @27
    @22
    @53
    @49
    simpr2r
    cgrtr4and
    @51
    @19
    @52
    @22
    @28
    @49
    simpr31
    cgrtrand
    sylan2br
    expr
    sylbid
    anim2d
    sylanb
    an32s
    reximdva
    mpd
    expr
    an32s
    rexlimdva
    @13
    @20
    @29
    wb
    #
    @22
    @13
    @0
    @2
    @3
    @5
    @6
    @63
    @0
    @2
    @3
    @8
    @12
    simp11
    #
    @0
    @2
    @3
    @8
    @12
    simp12
    @0
    @2
    @3
    @8
    @12
    simp13
    @4
    @5
    @6
    @7
    @12
    simp21
    @4
    @5
    @6
    @7
    @12
    simp22
    vy
    cA
    cB
    cC
    cD
    cN
    brsegle
    syl122anc
    adantr
    @13
    @21
    @35
    wb
    #
    @22
    @13
    @0
    @7
    @9
    @10
    @11
    @65
    @64
    @4
    @5
    @6
    @7
    @12
    simp23
    @4
    @8
    @9
    @10
    @11
    simp31
    @4
    @8
    @9
    @10
    @11
    simp32
    @4
    @8
    @9
    @10
    @11
    simp33
    vz
    cE
    cF
    cG
    cH
    cN
    brsegle
    syl122anc
    adantr
    3imtr4d
    exp32
    3impd
end
