include "crn.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cn0.mm"
include "crab.mm"
include "wral.mm"
include "cicc.mm"
include "cfv.mm"
include "weq.mm"
include "wi.mm"
include "wreu.mm"
include "cc0.mm"
include "cuz.mm"
include "wwe.mm"
include "cvv.mm"
include "wcel.mm"
include "ltweuz.mm"
include "a1i.mm"
include "nn0ex.mm"
include "rabex.mm"
include "ssrab2.mm"
include "nn0uz.mm"
include "sseqtri.mm"
include "id.mm"
include "cxp.mm"
include "cle.mm"
include "cr.mm"
include "cin.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "dyadf.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "rexcom.mm"
include "sylbb.mm"
include "rgen.mm"
include "ssralv.mm"
include "mpi.mm"
include "r19.2z.mm"
include "syl2anr.mm"
include "sylib.mm"
include "rabn0.mm"
include "sylibr.mm"
include "wereu.mm"
include "syl13anc.mm"
include "reurex.mm"
include "syl.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "2rexbidv.mm"
include "elrab.mm"
include "eqeq1.mm"
include "oveq1.mm"
include "cbvrex2v.mm"
include "syl5bb.mm"
include "ralrab.mm"
include "r19.23v.mm"
include "ralbii.mm"
include "ralcom.mm"
include "bitr3i.mm"
include "simplll.mm"
include "sselda.mm"
include "r19.29.mm"
include "expcom.mm"
include "sylbi.mm"
include "simplrr.mm"
include "ad2antrr.mm"
include "simp-5r.mm"
include "simplrl.mm"
include "simprl.mm"
include "simprr.mm"
include "dyadmaxlem.mm"
include "oveq12.mm"
include "exp32.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "eqeq2.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "a2d.mm"
include "impd.mm"
include "syld.mm"
include "ralimdva.mm"
include "syl5bi.mm"
include "imp.mm"
include "an32s.mm"
include "sseq1d.mm"
include "ralbidv.mm"
include "reximdva.mm"
include "ex.mm"
include "com23.mm"
include "expimpd.mm"
include "rexlimdv.mm"
include "mpd.mm"

theorem dyadmax
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cF: class F
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let cC: class C
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let wph: wff ph
  let vi: setvar i
  let vr: setvar r
  let cD: class D
  let cG: class G
  assume dyadmbl.1: |- F = ( x e. ZZ , y e. NN0 |-> <. ( x / ( 2 ^ y ) ) , ( ( x + 1 ) / ( 2 ^ y ) ) >. )

  disjoint x y
  disjoint w z
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c d
  disjoint c f
  disjoint c x
  disjoint c y
  disjoint d f
  disjoint d x
  disjoint d y
  disjoint f x
  disjoint f y
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint a y
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint a f
  disjoint a m
  disjoint a n
  disjoint a t
  disjoint a w
  disjoint a z
  disjoint a ph
  disjoint b f
  disjoint b m
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint b z
  disjoint b ph
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f w
  disjoint f z
  disjoint f ph
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m z
  disjoint m ph
  disjoint n t
  disjoint n w
  disjoint n z
  disjoint n ph
  disjoint t w
  disjoint t z
  disjoint ph t
  disjoint ph w
  disjoint ph z
  disjoint a i
  disjoint a r
  disjoint A a
  disjoint b i
  disjoint b r
  disjoint A b
  disjoint c i
  disjoint c m
  disjoint c n
  disjoint c r
  disjoint c t
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint d i
  disjoint d m
  disjoint d n
  disjoint d r
  disjoint d t
  disjoint d w
  disjoint d z
  disjoint A d
  disjoint i m
  disjoint i n
  disjoint i r
  disjoint i t
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint A i
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint r t
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint D x
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G f
  disjoint G m
  disjoint G n
  disjoint G t
  disjoint G z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F m
  disjoint F n
  disjoint F r
  assert |- ( ( A C_ ran F /\ A =/= (/) ) -> E. z e. A A. w e. A ( ( [,] ` z ) C_ ( [,] ` w ) -> z = w ) )

  proof
    cA
    cF
    crn
    #
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    vd
    cv
    #
    vc
    cv
    #
    clt
    wbr
    wn
    #
    vd
    vz
    cv
    #
    va
    cv
    #
    vn
    cv
    #
    cF
    co
    #
    wceq
    #
    va
    cz
    wrex
    #
    vz
    cA
    wrex
    #
    vn
    cn0
    crab
    #
    wral
    #
    vc
    @14
    wrex
    #
    @7
    cicc
    cfv
    #
    vw
    cv
    #
    cicc
    cfv
    #
    wss
    #
    vz
    vw
    weq
    #
    wi
    #
    vw
    cA
    wral
    #
    vz
    cA
    wrex
    #
    @3
    @15
    vc
    @14
    wreu
    #
    @16
    @3
    cc0
    cuz
    cfv
    #
    clt
    wwe
    #
    @14
    cvv
    wcel
    #
    @14
    @26
    wss
    #
    @14
    c0
    wne
    #
    @25
    @27
    @3
    cc0
    ltweuz
    a1i
    @28
    @3
    @13
    vn
    cn0
    nn0ex
    rabex
    a1i
    @29
    @3
    @14
    cn0
    @26
    @13
    vn
    cn0
    ssrab2
    nn0uz
    sseqtri
    a1i
    @3
    @13
    vn
    cn0
    wrex
    #
    @30
    @3
    @12
    vn
    cn0
    wrex
    #
    vz
    cA
    wrex
    #
    @31
    @2
    @2
    @32
    vz
    cA
    wral
    #
    @33
    @1
    @2
    id
    @1
    @32
    vz
    @0
    wral
    @34
    @32
    vz
    @0
    @7
    @0
    wcel
    #
    @11
    vn
    cn0
    wrex
    va
    cz
    wrex
    #
    @32
    cz
    cn0
    cxp
    #
    cle
    cr
    cr
    cxp
    cin
    #
    cF
    wf
    #
    cF
    @37
    wfn
    #
    @35
    @36
    wb
    vx
    vy
    cF
    dyadmbl.1
    dyadf
    #
    @37
    @38
    cF
    ffn
    #
    va
    vn
    cz
    cn0
    @7
    cF
    ovelrn
    mp2b
    @11
    va
    vn
    cz
    cn0
    rexcom
    sylbb
    rgen
    @32
    vz
    cA
    @0
    ssralv
    mpi
    @32
    vz
    cA
    r19.2z
    syl2anr
    @12
    vz
    vn
    cA
    cn0
    rexcom
    sylib
    @13
    vn
    cn0
    rabn0
    sylibr
    vc
    vd
    @26
    @14
    clt
    cvv
    wereu
    syl13anc
    @15
    vc
    @14
    reurex
    syl
    @3
    @15
    @24
    vc
    @14
    @5
    @14
    wcel
    @5
    cn0
    wcel
    #
    @7
    @8
    @5
    cF
    co
    #
    wceq
    #
    va
    cz
    wrex
    #
    vz
    cA
    wrex
    #
    wa
    @3
    @15
    @24
    wi
    #
    @13
    @47
    vn
    @5
    cn0
    vn
    vc
    weq
    #
    @11
    @45
    vz
    va
    cA
    cz
    @49
    @10
    @44
    @7
    @9
    @5
    @8
    cF
    oveq2
    eqeq2d
    2rexbidv
    elrab
    @3
    @43
    @47
    @48
    @3
    @43
    wa
    #
    @15
    @47
    @24
    @15
    @18
    vb
    cv
    #
    @4
    cF
    co
    #
    wceq
    #
    vb
    cz
    wrex
    #
    vw
    cA
    wrex
    #
    @6
    wi
    #
    vd
    cn0
    wral
    #
    @50
    @47
    @24
    wi
    #
    @13
    @55
    @6
    vd
    vn
    cn0
    @13
    @18
    @51
    @9
    cF
    co
    #
    wceq
    #
    vb
    cz
    wrex
    vw
    cA
    wrex
    vn
    vd
    weq
    #
    @55
    @11
    @60
    @18
    @10
    wceq
    vz
    va
    vw
    vb
    cA
    cz
    @7
    @18
    @10
    eqeq1
    va
    vb
    weq
    #
    @10
    @59
    @18
    @8
    @51
    @9
    cF
    oveq1
    eqeq2d
    cbvrex2v
    @61
    @60
    @53
    vw
    vb
    cA
    cz
    @61
    @59
    @52
    @18
    @9
    @4
    @51
    cF
    oveq2
    eqeq2d
    2rexbidv
    syl5bb
    ralrab
    @50
    @57
    @58
    @50
    @57
    wa
    #
    @46
    @23
    vz
    cA
    @63
    @7
    cA
    wcel
    #
    wa
    @45
    @23
    va
    cz
    @63
    @64
    @8
    cz
    wcel
    #
    @45
    @23
    wi
    @63
    @64
    @65
    wa
    #
    wa
    @23
    @45
    @44
    cicc
    cfv
    #
    @19
    wss
    #
    @44
    @18
    wceq
    #
    wi
    #
    vw
    cA
    wral
    #
    @50
    @66
    @57
    @71
    @50
    @66
    wa
    #
    @57
    @71
    @57
    @54
    @6
    wi
    #
    vd
    cn0
    wral
    #
    vw
    cA
    wral
    #
    @72
    @71
    @57
    @73
    vw
    cA
    wral
    #
    vd
    cn0
    wral
    @75
    @76
    @56
    vd
    cn0
    @54
    @6
    vw
    cA
    r19.23v
    ralbii
    @73
    vd
    vw
    cn0
    cA
    ralcom
    bitr3i
    @72
    @74
    @70
    vw
    cA
    @72
    @18
    cA
    wcel
    #
    wa
    #
    @74
    @73
    @54
    wa
    #
    vd
    cn0
    wrex
    #
    @70
    @78
    @53
    vd
    cn0
    wrex
    vb
    cz
    wrex
    #
    @74
    @80
    wi
    #
    @78
    @18
    @0
    wcel
    #
    @81
    @72
    cA
    @0
    @18
    @1
    @2
    @43
    @66
    simplll
    sselda
    @39
    @40
    @83
    @81
    wb
    @41
    @42
    vb
    vd
    cz
    cn0
    @18
    cF
    ovelrn
    mp2b
    sylib
    @81
    @54
    vd
    cn0
    wrex
    #
    @82
    @53
    vb
    vd
    cz
    cn0
    rexcom
    @74
    @84
    @80
    @73
    @54
    vd
    cn0
    r19.29
    expcom
    sylbi
    syl
    @78
    @79
    @70
    vd
    cn0
    @78
    @4
    cn0
    wcel
    #
    wa
    #
    @73
    @54
    @70
    @86
    @54
    @6
    @70
    @86
    @53
    @6
    @70
    wi
    #
    vb
    cz
    @78
    @85
    @51
    cz
    wcel
    #
    @53
    @87
    wi
    @78
    @85
    @88
    wa
    #
    wa
    #
    @87
    @53
    @6
    @67
    @52
    cicc
    cfv
    #
    wss
    #
    @44
    @52
    wceq
    #
    wi
    #
    wi
    @90
    @6
    @92
    @93
    @90
    @6
    @92
    wa
    #
    wa
    #
    @62
    vc
    vd
    weq
    wa
    @93
    @96
    vx
    vy
    @8
    @51
    @5
    @4
    cF
    dyadmbl.1
    @78
    @65
    @89
    @95
    @50
    @64
    @65
    @77
    simplrr
    ad2antrr
    @78
    @85
    @88
    @95
    simplrr
    @3
    @43
    @66
    @77
    @89
    @95
    simp-5r
    @78
    @85
    @88
    @95
    simplrl
    @90
    @6
    @92
    simprl
    @90
    @6
    @92
    simprr
    dyadmaxlem
    @8
    @51
    @5
    @4
    cF
    oveq12
    syl
    exp32
    @53
    @70
    @94
    @6
    @53
    @68
    @92
    @69
    @93
    @53
    @19
    @91
    @67
    @18
    @52
    cicc
    fveq2
    sseq2d
    @18
    @52
    @44
    eqeq2
    imbi12d
    imbi2d
    syl5ibrcom
    anassrs
    rexlimdva
    a2d
    impd
    rexlimdva
    syld
    ralimdva
    syl5bi
    imp
    an32s
    @45
    @22
    @70
    vw
    cA
    @45
    @20
    @68
    @21
    @69
    @45
    @17
    @67
    @19
    @7
    @44
    cicc
    fveq2
    sseq1d
    @7
    @44
    @18
    eqeq1
    imbi12d
    ralbidv
    syl5ibrcom
    anassrs
    rexlimdva
    reximdva
    ex
    syl5bi
    com23
    expimpd
    syl5bi
    rexlimdv
    mpd
end
