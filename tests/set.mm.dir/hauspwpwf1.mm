include "cha.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "ccl.mm"
include "cfv.mm"
include "cpw.mm"
include "wel.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "wf1.mm"
include "inss2.mm"
include "vex.mm"
include "inex1.mm"
include "elpw.mm"
include "mpbir.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "adantl.mm"
include "rexlimivw.mm"
include "abssi.mm"
include "cvv.mm"
include "wb.mm"
include "ctop.mm"
include "haustop.mm"
include "topopn.mm"
include "syl.mm"
include "ssexg.mm"
include "sylan2.mm"
include "ancoms.mm"
include "pwexg.mm"
include "elpw2g.mm"
include "3syl.mm"
include "a1d.mm"
include "weq.mm"
include "wne.mm"
include "c0.mm"
include "w3a.mm"
include "simplll.mm"
include "clsss3.mm"
include "sylan.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "sseldd.mm"
include "simplrr.mm"
include "simpr.mm"
include "hausnei.mm"
include "syl13anc.mm"
include "wn.mm"
include "simprll.mm"
include "simprr1.mm"
include "eqidd.mm"
include "elequ2.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "wi.mm"
include "wex.mm"
include "ad3antrrr.mm"
include "simplr.mm"
include "simprr.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "inopn.mm"
include "syl3anc.mm"
include "simpr2.mm"
include "elind.mm"
include "clsndisj.mm"
include "syl32anc.mm"
include "n0.mm"
include "sylib.mm"
include "elin.mm"
include "anbi1i.mm"
include "bitri.mm"
include "biimpri.mm"
include "adantll.mm"
include "ad2antll.mm"
include "simpll.mm"
include "simpr3.mm"
include "minel.mm"
include "inss1.mm"
include "sseli.mm"
include "nsyl.mm"
include "syl2anc.mm"
include "nelneq2.mm"
include "eqcom.mm"
include "sylnib.mm"
include "expr.mm"
include "syl5bi.mm"
include "exlimdv.mm"
include "mpd.mm"
include "anassrs.mm"
include "nan.mm"
include "nrexdv.mm"
include "sylnibr.mm"
include "nelne1.mm"
include "rexlimdvva.mm"
include "ex.mm"
include "necon4d.mm"
include "anbi1d.mm"
include "abbidv.mm"
include "impbid1.mm"
include "dom2lem.mm"
include "f1eq1.mm"
include "ax-mp.mm"

theorem hauspwpwf1
  let vx: setvar x
  let cA: class A
  let vj: setvar j
  let cF: class F
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  let vz: setvar z
  assume hauspwpwf1.x: |- X = U. J
  assume hauspwpwf1.f: |- F = ( x e. ( ( cls ` J ) ` A ) |-> { a | E. j e. J ( x e. j /\ a = ( j i^i A ) ) } )

  disjoint a j
  disjoint a x
  disjoint A a
  disjoint j x
  disjoint A j
  disjoint A x
  disjoint J a
  disjoint J j
  disjoint J x
  disjoint X j
  disjoint X x
  disjoint a k
  disjoint a l
  disjoint a y
  disjoint j k
  disjoint j l
  disjoint j y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint l x
  disjoint l y
  disjoint A l
  disjoint x y
  disjoint A y
  disjoint J k
  disjoint J l
  disjoint J y
  disjoint j z
  disjoint k z
  disjoint l z
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint X k
  disjoint X l
  disjoint X y
  disjoint X z
  disjoint J z
  assert |- ( ( J e. Haus /\ A C_ X ) -> F : ( ( cls ` J ) ` A ) -1-1-> ~P ~P A )

  proof
    cJ
    cha
    wcel
    #
    cA
    cX
    wss
    #
    wa
    #
    cA
    cJ
    ccl
    cfv
    cfv
    #
    cA
    cpw
    #
    cpw
    #
    vx
    @3
    vx
    vj
    wel
    #
    va
    cv
    #
    vj
    cv
    #
    cA
    cin
    #
    wceq
    #
    wa
    #
    vj
    cJ
    wrex
    #
    va
    cab
    #
    cmpt
    #
    wf1
    #
    @3
    @5
    cF
    wf1
    #
    @2
    vx
    vy
    @3
    @5
    @13
    vy
    vj
    wel
    #
    @10
    wa
    #
    vj
    cJ
    wrex
    #
    va
    cab
    #
    @2
    @13
    @5
    wcel
    #
    vx
    cv
    #
    @3
    wcel
    #
    @2
    @21
    @13
    @4
    wss
    #
    @12
    va
    @4
    @11
    @7
    @4
    wcel
    #
    vj
    cJ
    @10
    @25
    @6
    @10
    @25
    @9
    @4
    wcel
    #
    @26
    @9
    cA
    wss
    @8
    cA
    inss2
    @9
    cA
    @8
    cA
    vj
    vex
    inex1
    elpw
    mpbir
    @7
    @9
    @4
    eleq1
    mpbiri
    adantl
    rexlimivw
    abssi
    @2
    cA
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @21
    @24
    wb
    @1
    @0
    @27
    @0
    @1
    cX
    cJ
    wcel
    #
    @27
    @0
    cJ
    ctop
    wcel
    #
    @28
    cJ
    haustop
    #
    cJ
    cX
    hauspwpwf1.x
    topopn
    syl
    cA
    cX
    cJ
    ssexg
    sylan2
    ancoms
    cA
    cvv
    pwexg
    @13
    @4
    cvv
    elpw2g
    3syl
    mpbiri
    a1d
    @2
    @23
    vy
    cv
    #
    @3
    wcel
    #
    wa
    #
    @13
    @20
    wceq
    #
    vx
    vy
    weq
    #
    wb
    @2
    @33
    wa
    #
    @34
    @35
    @36
    @22
    @31
    @13
    @20
    @36
    @22
    @31
    wne
    #
    @13
    @20
    wne
    #
    @36
    @37
    wa
    #
    vx
    vk
    wel
    #
    vy
    vl
    wel
    #
    vk
    cv
    #
    vl
    cv
    #
    cin
    c0
    wceq
    #
    w3a
    #
    vl
    cJ
    wrex
    vk
    cJ
    wrex
    #
    @38
    @39
    @0
    @22
    cX
    wcel
    @31
    cX
    wcel
    @37
    @46
    @0
    @1
    @33
    @37
    simplll
    @39
    @3
    cX
    @22
    @2
    @3
    cX
    wss
    #
    @33
    @37
    @0
    @29
    @1
    @47
    @30
    cA
    cJ
    cX
    hauspwpwf1.x
    clsss3
    sylan
    ad2antrr
    #
    @2
    @23
    @32
    @37
    simplrl
    sseldd
    @39
    @3
    cX
    @31
    @48
    @2
    @23
    @32
    @37
    simplrr
    sseldd
    @36
    @37
    simpr
    @22
    @31
    vl
    vk
    cJ
    cX
    hauspwpwf1.x
    hausnei
    syl13anc
    @39
    @45
    @38
    vk
    vl
    cJ
    cJ
    @39
    @42
    cJ
    wcel
    #
    @43
    cJ
    wcel
    #
    wa
    #
    @45
    @38
    @39
    @51
    @45
    wa
    #
    wa
    #
    @42
    cA
    cin
    #
    @13
    wcel
    #
    @54
    @20
    wcel
    #
    wn
    @38
    @53
    @6
    @54
    @9
    wceq
    #
    wa
    #
    vj
    cJ
    wrex
    #
    @55
    @53
    @49
    @40
    @54
    @54
    wceq
    #
    @59
    @39
    @49
    @50
    @45
    simprll
    @40
    @41
    @44
    @51
    @39
    simprr1
    @53
    @54
    eqidd
    @58
    @40
    @60
    wa
    vj
    @42
    cJ
    vj
    vk
    weq
    #
    @6
    @40
    @57
    @60
    vj
    vk
    vx
    elequ2
    @61
    @9
    @54
    @54
    @8
    @42
    cA
    ineq1
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    @12
    @59
    va
    @54
    @42
    cA
    vk
    vex
    inex1
    #
    @7
    @54
    wceq
    #
    @11
    @58
    vj
    cJ
    @63
    @10
    @57
    @6
    @7
    @54
    @9
    eqeq1
    #
    anbi2d
    rexbidv
    elab
    sylibr
    @53
    @17
    @57
    wa
    #
    vj
    cJ
    wrex
    #
    @56
    @53
    @65
    vj
    cJ
    @53
    @8
    cJ
    wcel
    #
    wa
    #
    @65
    wn
    wi
    @68
    @17
    wa
    @57
    wn
    #
    wi
    @53
    @67
    @17
    @69
    @53
    @67
    @17
    wa
    #
    wa
    #
    vz
    cv
    #
    @43
    @8
    cin
    #
    cA
    cin
    #
    wcel
    #
    vz
    wex
    #
    @69
    @71
    @74
    c0
    wne
    #
    @76
    @71
    @29
    @1
    @32
    @73
    cJ
    wcel
    #
    @31
    @73
    wcel
    @77
    @36
    @29
    @37
    @52
    @70
    @0
    @29
    @1
    @33
    @30
    ad2antrr
    ad3antrrr
    #
    @36
    @1
    @37
    @52
    @70
    @0
    @1
    @33
    simplr
    ad3antrrr
    @36
    @32
    @37
    @52
    @70
    @2
    @23
    @32
    simprr
    ad3antrrr
    @71
    @29
    @50
    @67
    @78
    @79
    @52
    @50
    @39
    @70
    @49
    @50
    @45
    simplr
    ad2antlr
    @53
    @67
    @17
    simprl
    @43
    @8
    cJ
    inopn
    syl3anc
    @71
    @43
    @8
    @31
    @52
    @41
    @39
    @70
    @51
    @40
    @41
    @44
    simpr2
    ad2antlr
    @53
    @67
    @17
    simprr
    elind
    @31
    cA
    @73
    cJ
    cX
    hauspwpwf1.x
    clsndisj
    syl32anc
    vz
    @74
    n0
    sylib
    @71
    @75
    @69
    vz
    @75
    vz
    vl
    wel
    #
    vz
    vj
    wel
    #
    wa
    #
    @72
    cA
    wcel
    #
    wa
    #
    @71
    @69
    @75
    @72
    @73
    wcel
    #
    @83
    wa
    @84
    @72
    @73
    cA
    elin
    @85
    @82
    @83
    @72
    @43
    @8
    elin
    anbi1i
    bitri
    @53
    @70
    @84
    @69
    @53
    @70
    @84
    wa
    #
    wa
    #
    @9
    @54
    wceq
    #
    @57
    @87
    @72
    @9
    wcel
    #
    @72
    @54
    wcel
    #
    wn
    #
    @88
    wn
    @84
    @89
    @53
    @70
    @81
    @83
    @89
    @80
    @89
    @81
    @83
    wa
    @72
    @8
    cA
    elin
    biimpri
    adantll
    ad2antll
    @87
    @80
    @44
    @91
    @84
    @80
    @53
    @70
    @80
    @81
    @83
    simpll
    ad2antll
    @52
    @44
    @39
    @86
    @51
    @40
    @41
    @44
    simpr3
    ad2antlr
    @80
    @44
    wa
    vz
    vk
    wel
    @90
    @72
    @43
    @42
    minel
    @54
    @42
    @72
    @42
    cA
    inss1
    sseli
    nsyl
    syl2anc
    @72
    @9
    @54
    nelneq2
    syl2anc
    @9
    @54
    eqcom
    sylnib
    expr
    syl5bi
    exlimdv
    mpd
    anassrs
    @68
    @17
    @57
    nan
    mpbir
    nrexdv
    @19
    @66
    va
    @54
    @62
    @63
    @18
    @65
    vj
    cJ
    @63
    @10
    @57
    @17
    @64
    anbi2d
    rexbidv
    elab
    sylnibr
    @54
    @13
    @20
    nelne1
    syl2anc
    expr
    rexlimdvva
    mpd
    ex
    necon4d
    @35
    @12
    @19
    va
    @35
    @11
    @18
    vj
    cJ
    @35
    @6
    @17
    @10
    @22
    @31
    @8
    eleq1
    anbi1d
    rexbidv
    abbidv
    impbid1
    ex
    dom2lem
    cF
    @14
    wceq
    @16
    @15
    wb
    hauspwpwf1.f
    @3
    @5
    cF
    @14
    f1eq1
    ax-mp
    sylibr
end
