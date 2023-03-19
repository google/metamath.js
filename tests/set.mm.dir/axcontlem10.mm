include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cop.mm"
include "cbtwn.mm"
include "wbr.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cle.mm"
include "cima.mm"
include "cr.mm"
include "wrex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "crn.mm"
include "imassrn.mm"
include "wf1o.mm"
include "wfo.mm"
include "wceq.mm"
include "simpll.mm"
include "simprl1.mm"
include "simplr1.mm"
include "simprl2.mm"
include "sseldd.mm"
include "simprr.mm"
include "axcontlem2.mm"
include "syl31anc.mm"
include "f1ofo.mm"
include "forn.mm"
include "3syl.mm"
include "syl5sseq.mm"
include "rge0ssre.mm"
include "syl6ss.mm"
include "axcontlem9.mm"
include "dedekindle.mm"
include "syl3anc.mm"
include "wi.mm"
include "simpr.mm"
include "wex.mm"
include "simprl3.mm"
include "ad2antrr.mm"
include "n0.mm"
include "sylib.mm"
include "0red.mm"
include "wf.mm"
include "f1of.mm"
include "syl.mm"
include "axcontlem4.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "simprl.mm"
include "elrege0.mm"
include "simprbi.mm"
include "wf1.mm"
include "wb.mm"
include "f1of1.mm"
include "f1elima.mm"
include "mpbird.mm"
include "adantr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "3jca.mm"
include "axcontlem3.mm"
include "sylan2.mm"
include "sselda.mm"
include "adantrl.mm"
include "jca.mm"
include "breq1.mm"
include "anbi1d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "rspc2va.mm"
include "sylan.mm"
include "an32s.mm"
include "simpld.mm"
include "letrd.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ccnv.mm"
include "wo.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "f1ocnvdm.mm"
include "syl2an.mm"
include "adantrr.mm"
include "simplr.mm"
include "wfun.mm"
include "cdm.mm"
include "f1ofun.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funfvima2.mm"
include "syl2anc.mm"
include "anim12d.mm"
include "imp.mm"
include "simprll.mm"
include "rspc2v.mm"
include "sylc.mm"
include "f1ocnvfv2.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "axcontlem8.mm"
include "anassrs.mm"
include "ralrimivva.mm"
include "weq.mm"
include "opeq1.mm"
include "opeq2.mm"
include "cbvral2v.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "syld.mm"
include "com23.mm"
include "rexlimdv.mm"

theorem axcontlem10
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cU: class U
  let vi: setvar i
  let cF: class F
  let cN: class N
  let cZ: class Z
  let vp: setvar p
  let vb: setvar b
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vq: setvar q
  let vr: setvar r
  assume axcontlem10.1: |- D = { p e. ( EE ` N ) | ( U Btwn <. Z , p >. \/ p Btwn <. Z , U >. ) }
  assume axcontlem10.2: |- F = { <. x , t >. | ( x e. D /\ ( t e. ( 0 [,) +oo ) /\ A. i e. ( 1 ... N ) ( x ` i ) = ( ( ( 1 - t ) x. ( Z ` i ) ) + ( t x. ( U ` i ) ) ) ) ) }

  disjoint A b
  disjoint A p
  disjoint A x
  disjoint b p
  disjoint b x
  disjoint p x
  disjoint B b
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint b y
  disjoint p y
  disjoint x y
  disjoint D p
  disjoint D t
  disjoint D x
  disjoint p t
  disjoint t x
  disjoint F b
  disjoint F i
  disjoint i p
  disjoint i t
  disjoint i x
  disjoint F p
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint N b
  disjoint N i
  disjoint N p
  disjoint N t
  disjoint N x
  disjoint N y
  disjoint U b
  disjoint U i
  disjoint U p
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint Z b
  disjoint Z i
  disjoint Z p
  disjoint Z t
  disjoint Z x
  disjoint Z y
  disjoint A k
  disjoint A m
  disjoint A n
  disjoint A q
  disjoint A r
  disjoint k m
  disjoint k n
  disjoint k q
  disjoint k r
  disjoint m n
  disjoint m q
  disjoint m r
  disjoint n q
  disjoint n r
  disjoint q r
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b q
  disjoint b r
  disjoint B k
  disjoint B m
  disjoint B n
  disjoint B q
  disjoint B r
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F q
  disjoint F r
  disjoint i k
  disjoint i m
  disjoint i n
  disjoint i q
  disjoint i r
  disjoint k p
  disjoint m p
  disjoint n p
  disjoint p q
  disjoint p r
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N q
  disjoint N r
  disjoint k t
  disjoint m t
  disjoint n t
  disjoint q t
  disjoint r t
  disjoint U k
  disjoint U m
  disjoint U n
  disjoint U q
  disjoint U r
  disjoint k x
  disjoint m x
  disjoint n x
  disjoint q x
  disjoint r x
  disjoint k y
  disjoint m y
  disjoint n y
  disjoint q y
  disjoint r y
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z q
  disjoint Z r
  assert |- ( ( ( N e. NN /\ ( A C_ ( EE ` N ) /\ B C_ ( EE ` N ) /\ A. x e. A A. y e. B x Btwn <. Z , y >. ) ) /\ ( ( Z e. ( EE ` N ) /\ U e. A /\ B =/= (/) ) /\ Z =/= U ) ) -> E. b e. ( EE ` N ) A. x e. A A. y e. B b Btwn <. x , y >. )

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
    wss
    #
    cB
    @1
    wss
    #
    vx
    cv
    #
    cZ
    vy
    cv
    #
    cop
    cbtwn
    wbr
    vy
    cB
    wral
    vx
    cA
    wral
    #
    w3a
    #
    wa
    #
    cZ
    @1
    wcel
    #
    cU
    cA
    wcel
    #
    cB
    c0
    wne
    #
    w3a
    #
    cZ
    cU
    wne
    #
    wa
    #
    wa
    #
    vm
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    @17
    vn
    cv
    #
    cle
    wbr
    #
    wa
    #
    vn
    cF
    cB
    cima
    #
    wral
    vm
    cF
    cA
    cima
    #
    wral
    #
    vk
    cr
    wrex
    #
    vb
    cv
    #
    @4
    @5
    cop
    #
    cbtwn
    wbr
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    vb
    @1
    wrex
    #
    @15
    @23
    cr
    wss
    @22
    cr
    wss
    @16
    @19
    cle
    wbr
    vn
    @22
    wral
    vm
    @23
    wral
    @25
    @15
    @23
    cc0
    cpnf
    cico
    co
    #
    cr
    @15
    cF
    crn
    #
    @23
    @31
    cF
    cA
    imassrn
    @15
    cD
    @31
    cF
    wf1o
    #
    cD
    @31
    cF
    wfo
    @32
    @31
    wceq
    @15
    @0
    @9
    cU
    @1
    wcel
    #
    @13
    @33
    @0
    @7
    @14
    simpll
    #
    @9
    @10
    @11
    @13
    @8
    simprl1
    #
    @15
    cA
    @1
    cU
    @2
    @3
    @6
    @0
    @14
    simplr1
    @9
    @10
    @11
    @13
    @8
    simprl2
    #
    sseldd
    #
    @8
    @12
    @13
    simprr
    #
    vx
    vt
    cD
    cU
    vi
    cF
    cN
    cZ
    vp
    axcontlem10.1
    axcontlem10.2
    axcontlem2
    syl31anc
    #
    cD
    @31
    cF
    f1ofo
    cD
    @31
    cF
    forn
    3syl
    #
    syl5sseq
    rge0ssre
    syl6ss
    @15
    @22
    @31
    cr
    @15
    @32
    @22
    @31
    cF
    cB
    imassrn
    @41
    syl5sseq
    rge0ssre
    syl6ss
    vx
    vy
    vt
    cA
    cB
    cD
    cU
    vi
    vn
    vm
    cF
    cN
    cZ
    vp
    axcontlem10.1
    axcontlem10.2
    axcontlem9
    vm
    vn
    vk
    @23
    @22
    dedekindle
    syl3anc
    @15
    @24
    @30
    vk
    cr
    @15
    @24
    @17
    cr
    wcel
    #
    @30
    @15
    @24
    @42
    @30
    wi
    @15
    @24
    wa
    #
    @42
    @17
    @31
    wcel
    #
    @30
    @43
    @42
    @44
    @43
    @42
    wa
    #
    @42
    cc0
    @17
    cle
    wbr
    #
    @44
    @43
    @42
    simpr
    @45
    @26
    cB
    wcel
    #
    vb
    wex
    #
    @46
    @45
    @11
    @48
    @15
    @11
    @24
    @42
    @9
    @10
    @11
    @13
    @8
    simprl3
    ad2antrr
    vb
    cB
    n0
    sylib
    @45
    @47
    @46
    vb
    @43
    @42
    @47
    @46
    @43
    @42
    @47
    wa
    #
    wa
    #
    cc0
    cU
    cF
    cfv
    #
    @17
    @50
    0red
    @15
    @51
    cr
    wcel
    #
    @24
    @49
    @15
    @31
    cr
    @51
    rge0ssre
    @15
    cD
    @31
    cU
    cF
    @15
    @33
    cD
    @31
    cF
    wf
    #
    @40
    cD
    @31
    cF
    f1of
    #
    syl
    @15
    cA
    cD
    cU
    vx
    vy
    cA
    cB
    cD
    cU
    cN
    cZ
    vp
    axcontlem10.1
    axcontlem4
    #
    @37
    sseldd
    #
    ffvelrnd
    #
    sseldi
    ad2antrr
    @43
    @42
    @47
    simprl
    @15
    cc0
    @51
    cle
    wbr
    #
    @24
    @49
    @15
    @51
    @31
    wcel
    #
    @58
    @57
    @59
    @52
    @58
    @51
    elrege0
    simprbi
    syl
    ad2antrr
    @50
    @51
    @17
    cle
    wbr
    #
    @17
    @26
    cF
    cfv
    #
    cle
    wbr
    #
    @15
    @49
    @24
    @60
    @62
    wa
    #
    @15
    @49
    wa
    #
    @51
    @23
    wcel
    #
    @61
    @22
    wcel
    #
    wa
    @24
    @63
    @64
    @65
    @66
    @15
    @65
    @49
    @15
    @65
    @10
    @37
    @15
    cD
    @31
    cF
    wf1
    #
    cU
    cD
    wcel
    cA
    cD
    wss
    @65
    @10
    wb
    @15
    @33
    @67
    @40
    cD
    @31
    cF
    f1of1
    syl
    #
    @56
    @55
    cD
    @31
    cF
    cU
    cA
    f1elima
    syl3anc
    mpbird
    adantr
    @15
    @47
    @66
    @42
    @15
    @47
    wa
    #
    @66
    @47
    @15
    @47
    simpr
    @69
    @67
    @26
    cD
    wcel
    cB
    cD
    wss
    #
    @66
    @47
    wb
    @15
    @67
    @47
    @68
    adantr
    @15
    cB
    cD
    @26
    @14
    @8
    @9
    @10
    @13
    w3a
    @70
    @14
    @9
    @10
    @13
    @9
    @10
    @11
    @13
    simpl1
    @9
    @10
    @11
    @13
    simpl2
    @12
    @13
    simpr
    3jca
    vx
    vy
    cA
    cB
    cD
    cU
    cN
    cZ
    vp
    axcontlem10.1
    axcontlem3
    sylan2
    #
    sselda
    @15
    @70
    @47
    @71
    adantr
    cD
    @31
    cF
    @26
    cB
    f1elima
    syl3anc
    mpbird
    adantrl
    jca
    @21
    @63
    @60
    @20
    wa
    vm
    vn
    @51
    @61
    @23
    @22
    @16
    @51
    wceq
    @18
    @60
    @20
    @16
    @51
    @17
    cle
    breq1
    anbi1d
    @19
    @61
    wceq
    @20
    @62
    @60
    @19
    @61
    @17
    cle
    breq2
    anbi2d
    rspc2va
    sylan
    an32s
    simpld
    letrd
    expr
    exlimdv
    mpd
    @17
    elrege0
    sylanbrc
    ex
    @15
    @24
    @44
    @30
    @15
    @24
    @44
    wa
    #
    wa
    #
    @17
    cF
    ccnv
    cfv
    #
    @1
    wcel
    @74
    @27
    cbtwn
    wbr
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    @30
    @73
    cD
    @1
    @74
    cD
    cU
    cZ
    vp
    cv
    #
    cop
    cbtwn
    wbr
    @77
    cZ
    cU
    cop
    cbtwn
    wbr
    wo
    #
    vp
    @1
    crab
    @1
    axcontlem10.1
    @78
    vp
    @1
    ssrab2
    eqsstri
    @15
    @33
    @44
    @74
    cD
    wcel
    #
    @72
    @40
    @24
    @44
    simpr
    cD
    @31
    @17
    cF
    f1ocnvdm
    #
    syl2an
    sseldi
    @73
    @74
    vq
    cv
    #
    vr
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    vr
    cB
    wral
    vq
    cA
    wral
    @76
    @73
    @84
    vq
    vr
    cA
    cB
    @15
    @72
    @81
    cA
    wcel
    #
    @82
    cB
    wcel
    #
    wa
    #
    @84
    @15
    @72
    @87
    wa
    #
    wa
    #
    @0
    @9
    @34
    w3a
    #
    @13
    wa
    #
    @81
    cD
    wcel
    #
    @79
    @82
    cD
    wcel
    #
    w3a
    #
    wa
    @81
    cF
    cfv
    #
    @74
    cF
    cfv
    #
    cle
    wbr
    #
    @96
    @82
    cF
    cfv
    #
    cle
    wbr
    #
    wa
    #
    @84
    @89
    @91
    @94
    @15
    @91
    @88
    @15
    @90
    @13
    @15
    @0
    @9
    @34
    @35
    @36
    @38
    3jca
    @39
    jca
    adantr
    @89
    @92
    @79
    @93
    @15
    @87
    @92
    @72
    @15
    @85
    @92
    @86
    @15
    cA
    cD
    @81
    @55
    sselda
    adantrr
    adantrl
    @15
    @33
    @44
    @79
    @88
    @40
    @24
    @44
    @87
    simplr
    #
    @80
    syl2an
    @15
    @87
    @93
    @72
    @15
    @86
    @93
    @85
    @15
    cB
    cD
    @82
    @71
    sselda
    adantrl
    adantrl
    3jca
    jca
    @89
    @100
    @95
    @17
    cle
    wbr
    #
    @17
    @98
    cle
    wbr
    #
    wa
    #
    @89
    @95
    @23
    wcel
    #
    @98
    @22
    wcel
    #
    wa
    #
    @24
    @104
    @15
    @87
    @107
    @72
    @15
    @87
    @107
    @15
    @85
    @105
    @86
    @106
    @15
    cF
    wfun
    #
    cA
    cF
    cdm
    #
    wss
    @85
    @105
    wi
    @15
    @33
    @108
    @40
    cD
    @31
    cF
    f1ofun
    syl
    #
    @15
    cA
    cD
    @109
    @55
    @15
    @33
    @53
    @109
    cD
    wceq
    @40
    @54
    cD
    @31
    cF
    fdm
    3syl
    #
    sseqtr4d
    cA
    @81
    cF
    funfvima2
    syl2anc
    @15
    @108
    cB
    @109
    wss
    @86
    @106
    wi
    @110
    @15
    cB
    cD
    @109
    @71
    @111
    sseqtr4d
    cB
    @82
    cF
    funfvima2
    syl2anc
    anim12d
    imp
    adantrl
    @15
    @24
    @44
    @87
    simprll
    @21
    @104
    @102
    @20
    wa
    vm
    vn
    @95
    @98
    @23
    @22
    @16
    @95
    wceq
    @18
    @102
    @20
    @16
    @95
    @17
    cle
    breq1
    anbi1d
    @19
    @98
    wceq
    @20
    @103
    @102
    @19
    @98
    @17
    cle
    breq2
    anbi2d
    rspc2v
    sylc
    @89
    @97
    @102
    @99
    @103
    @89
    @96
    @17
    @95
    cle
    @15
    @33
    @44
    @96
    @17
    wceq
    @88
    @40
    @101
    cD
    @31
    @17
    cF
    f1ocnvfv2
    syl2an
    #
    breq2d
    @89
    @96
    @17
    @98
    cle
    @112
    breq1d
    anbi12d
    mpbird
    vx
    vt
    cD
    @81
    @74
    @82
    cU
    vi
    cF
    cN
    cZ
    vp
    axcontlem10.1
    axcontlem10.2
    axcontlem8
    sylc
    anassrs
    ralrimivva
    @84
    @75
    @74
    @4
    @82
    cop
    #
    cbtwn
    wbr
    vq
    vr
    vx
    vy
    cA
    cB
    vq
    vx
    weq
    @83
    @113
    @74
    cbtwn
    @81
    @4
    @82
    opeq1
    breq2d
    vr
    vy
    weq
    @113
    @27
    @74
    cbtwn
    @82
    @5
    @4
    opeq2
    breq2d
    cbvral2v
    sylib
    @29
    @76
    vb
    @74
    @1
    @26
    @74
    wceq
    @28
    @75
    vx
    vy
    cA
    cB
    @26
    @74
    @27
    cbtwn
    breq1
    2ralbidv
    rspcev
    syl2anc
    expr
    syld
    ex
    com23
    rexlimdv
    mpd
end
