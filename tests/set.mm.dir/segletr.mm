include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "ccgr.mm"
include "wa.mm"
include "wrex.mm"
include "csegle.mm"
include "ccgr3.mm"
include "simprll.mm"
include "simprrr.mm"
include "jca.mm"
include "wi.mm"
include "simpl1.mm"
include "simpl23.mm"
include "simprl.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simprr.mm"
include "cgrxfr.mm"
include "syl132anc.mm"
include "adantr.mm"
include "mpd.mm"
include "anass.mm"
include "df-3an.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "wb.mm"
include "simpr1.mm"
include "simpr3.mm"
include "simpr2.mm"
include "brcgr3.mm"
include "syl133anc.mm"
include "anbi2d.mm"
include "simpl33.mm"
include "simpr3l.mm"
include "simpr2l.mm"
include "btwnexchand.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpr1r.mm"
include "simp3r1.mm"
include "adantl.mm"
include "cgrtrand.mm"
include "sylan2br.mm"
include "expr.mm"
include "sylbid.mm"
include "sylanb.mm"
include "an32s.mm"
include "reximdva.mm"
include "exp31.mm"
include "rexlimdvv.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31.mm"
include "brsegle.mm"
include "syl122anc.mm"
include "simp32.mm"
include "simp33.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "syl6bbr.mm"
include "3imtr4d.mm"

theorem segletr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cN: class N
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) /\ ( D e. ( EE ` N ) /\ E e. ( EE ` N ) /\ F e. ( EE ` N ) ) ) -> ( ( <. A , B >. Seg<_ <. C , D >. /\ <. C , D >. Seg<_ <. E , F >. ) -> <. A , B >. Seg<_ <. E , F >. ) )

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
    vy
    cv
    #
    cC
    cD
    cop
    #
    cbtwn
    wbr
    #
    cA
    cB
    cop
    #
    cC
    @11
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vz
    cv
    #
    cE
    cF
    cop
    #
    cbtwn
    wbr
    #
    @12
    cE
    @18
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    wa
    #
    vz
    @1
    wrex
    vy
    @1
    wrex
    #
    vw
    cv
    #
    @19
    cbtwn
    wbr
    #
    @14
    cE
    @26
    cop
    #
    ccgr
    wbr
    #
    wa
    #
    vw
    @1
    wrex
    #
    @14
    @12
    csegle
    wbr
    #
    @12
    @19
    csegle
    wbr
    #
    wa
    #
    @14
    @19
    csegle
    wbr
    #
    @10
    @24
    @31
    vy
    vz
    @1
    @1
    @10
    @11
    @1
    wcel
    #
    @18
    @1
    wcel
    #
    wa
    #
    @24
    @31
    @10
    @38
    wa
    #
    @24
    wa
    #
    @26
    @21
    cbtwn
    wbr
    #
    cC
    @11
    cD
    cop
    #
    cop
    cE
    @26
    @18
    cop
    #
    cop
    ccgr3
    wbr
    #
    wa
    #
    vw
    @1
    wrex
    #
    @31
    @40
    @13
    @22
    wa
    #
    @46
    @40
    @13
    @22
    @39
    @13
    @16
    @23
    simprll
    @39
    @17
    @20
    @22
    simprrr
    jca
    @39
    @47
    @46
    wi
    #
    @24
    @39
    @0
    @4
    @36
    @6
    @7
    @37
    @48
    @0
    @5
    @9
    @38
    simpl1
    @2
    @3
    @4
    @0
    @9
    @38
    simpl23
    @10
    @36
    @37
    simprl
    @6
    @7
    @8
    @0
    @5
    @38
    simpl31
    @6
    @7
    @8
    @0
    @5
    @38
    simpl32
    @10
    @36
    @37
    simprr
    cC
    @11
    cD
    cE
    vw
    @18
    cN
    cgrxfr
    syl132anc
    adantr
    mpd
    @40
    @45
    @30
    vw
    @1
    @39
    @26
    @1
    wcel
    #
    @24
    @45
    @30
    wi
    #
    @39
    @49
    wa
    #
    @10
    @36
    @37
    @49
    w3a
    #
    wa
    #
    @24
    @50
    @51
    @10
    @38
    @49
    wa
    #
    wa
    @53
    @10
    @38
    @49
    anass
    @52
    @54
    @10
    @36
    @37
    @49
    df-3an
    anbi2i
    bitr4i
    @53
    @24
    wa
    @45
    @41
    @15
    @28
    ccgr
    wbr
    #
    @22
    @42
    @43
    ccgr
    wbr
    #
    w3a
    #
    wa
    #
    @30
    @53
    @45
    @58
    wb
    @24
    @53
    @44
    @57
    @41
    @53
    @0
    @4
    @36
    @6
    @7
    @49
    @37
    @44
    @57
    wb
    @0
    @5
    @9
    @52
    simpl1
    #
    @2
    @3
    @4
    @0
    @9
    @52
    simpl23
    #
    @10
    @36
    @37
    @49
    simpr1
    #
    @6
    @7
    @8
    @0
    @5
    @52
    simpl31
    @6
    @7
    @8
    @0
    @5
    @52
    simpl32
    #
    @10
    @36
    @37
    @49
    simpr3
    #
    @10
    @36
    @37
    @49
    simpr2
    #
    cC
    @11
    cD
    cE
    @26
    @18
    cN
    brcgr3
    syl133anc
    anbi2d
    adantr
    @53
    @24
    @58
    @30
    @24
    @58
    wa
    @53
    @17
    @23
    @58
    w3a
    #
    @30
    @17
    @23
    @58
    df-3an
    @53
    @65
    wa
    @27
    @29
    @53
    @65
    cE
    @26
    @18
    cF
    cN
    @59
    @62
    @63
    @64
    @6
    @7
    @8
    @0
    @5
    @52
    simpl33
    @41
    @57
    @17
    @23
    @53
    simpr3l
    @20
    @22
    @17
    @58
    @53
    simpr2l
    btwnexchand
    @53
    @65
    cA
    cB
    cC
    @11
    cE
    @26
    cN
    @59
    @2
    @3
    @4
    @0
    @9
    @52
    simpl21
    @2
    @3
    @4
    @0
    @9
    @52
    simpl22
    @60
    @61
    @62
    @63
    @13
    @16
    @23
    @58
    @53
    simpr1r
    @65
    @55
    @53
    @55
    @22
    @56
    @41
    @17
    @23
    simp3r1
    adantl
    cgrtrand
    jca
    sylan2br
    expr
    sylbid
    sylanb
    an32s
    reximdva
    mpd
    exp31
    rexlimdvv
    @10
    @34
    @17
    vy
    @1
    wrex
    #
    @23
    vz
    @1
    wrex
    #
    wa
    @25
    @10
    @32
    @66
    @33
    @67
    @10
    @0
    @2
    @3
    @4
    @6
    @32
    @66
    wb
    @0
    @5
    @9
    simp1
    #
    @0
    @2
    @3
    @4
    @9
    simp21
    #
    @0
    @2
    @3
    @4
    @9
    simp22
    #
    @0
    @2
    @3
    @4
    @9
    simp23
    #
    @0
    @5
    @6
    @7
    @8
    simp31
    #
    vy
    cA
    cB
    cC
    cD
    cN
    brsegle
    syl122anc
    @10
    @0
    @4
    @6
    @7
    @8
    @33
    @67
    wb
    @68
    @71
    @72
    @0
    @5
    @6
    @7
    @8
    simp32
    #
    @0
    @5
    @6
    @7
    @8
    simp33
    #
    vz
    cC
    cD
    cE
    cF
    cN
    brsegle
    syl122anc
    anbi12d
    @17
    @23
    vy
    vz
    @1
    @1
    reeanv
    syl6bbr
    @10
    @0
    @2
    @3
    @7
    @8
    @35
    @31
    wb
    @68
    @69
    @70
    @73
    @74
    vw
    cA
    cB
    cE
    cF
    cN
    brsegle
    syl122anc
    3imtr4d
end
