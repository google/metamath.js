include "cop.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wcel.mm"
include "opex.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "3anbi1d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "3anbi2d.mm"
include "brab.mm"
include "wa.mm"
include "wi.mm"
include "wb.mm"
include "vex.mm"
include "opth.mm"
include "sylan9bb.mm"
include "sylbi.mm"
include "biimp3a.mm"
include "a1i.mm"
include "rexlimdva.mm"
include "rexlimdvva.mm"
include "simpl1.mm"
include "simpl2.mm"
include "opeq1.mm"
include "eqeq1d.mm"
include "3anbi23d.mm"
include "opeq2d.mm"
include "opeq2.mm"
include "eqid.mm"
include "pm3.2i.mm"
include "df-3an.mm"
include "mpbiran.mm"
include "rspc3ev.mm"
include "3ad2antl3.mm"
include "3anbi13d.mm"
include "syl2anc.mm"
include "rexeqdv.mm"
include "rexeqbidv.mm"
include "rspcev.mm"
include "ex.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem br6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let ve: setvar e
  let vf: setvar f
  let cE: class E
  let cF: class F
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume br6.1: |- ( a = A -> ( ph <-> ps ) )
  assume br6.2: |- ( b = B -> ( ps <-> ch ) )
  assume br6.3: |- ( c = C -> ( ch <-> th ) )
  assume br6.4: |- ( d = D -> ( th <-> ta ) )
  assume br6.5: |- ( e = E -> ( ta <-> et ) )
  assume br6.6: |- ( f = F -> ( et <-> ze ) )
  assume br6.7: |- ( x = X -> P = Q )
  assume br6.8: |- R = { <. p , q >. | E. x e. S E. a e. P E. b e. P E. c e. P E. d e. P E. e e. P E. f e. P ( p = <. a , <. b , c >. >. /\ q = <. d , <. e , f >. >. /\ ph ) }

  disjoint b ch
  disjoint e et
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a p
  disjoint a q
  disjoint P a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b p
  disjoint b q
  disjoint P b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c p
  disjoint c q
  disjoint P c
  disjoint d e
  disjoint d f
  disjoint d p
  disjoint d q
  disjoint P d
  disjoint e f
  disjoint e p
  disjoint e q
  disjoint P e
  disjoint f p
  disjoint f q
  disjoint P f
  disjoint p q
  disjoint P p
  disjoint P q
  disjoint p x
  disjoint p ph
  disjoint q x
  disjoint ph q
  disjoint ph x
  disjoint a ps
  disjoint a x
  disjoint A a
  disjoint b x
  disjoint A b
  disjoint c x
  disjoint A c
  disjoint d x
  disjoint A d
  disjoint e x
  disjoint A e
  disjoint f x
  disjoint A f
  disjoint A p
  disjoint A q
  disjoint A x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B p
  disjoint B q
  disjoint B x
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint Q e
  disjoint Q f
  disjoint Q x
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C p
  disjoint C q
  disjoint C x
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D p
  disjoint D q
  disjoint D x
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X e
  disjoint X f
  disjoint X x
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E d
  disjoint E e
  disjoint E f
  disjoint E p
  disjoint E q
  disjoint E x
  disjoint d ta
  disjoint c th
  disjoint a ze
  disjoint b ze
  disjoint c ze
  disjoint d ze
  disjoint e ze
  disjoint f ze
  disjoint x ze
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F p
  disjoint F q
  disjoint F x
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S p
  disjoint S q
  disjoint S x
  assert |- ( ( X e. S /\ ( A e. Q /\ B e. Q /\ C e. Q ) /\ ( D e. Q /\ E e. Q /\ F e. Q ) ) -> ( <. A , <. B , C >. >. R <. D , <. E , F >. >. <-> ze ) )

  proof
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
    cR
    wbr
    va
    cv
    #
    vb
    cv
    #
    vc
    cv
    #
    cop
    #
    cop
    #
    @1
    wceq
    #
    vd
    cv
    #
    ve
    cv
    #
    vf
    cv
    #
    cop
    #
    cop
    #
    @3
    wceq
    #
    wph
    w3a
    #
    vf
    cP
    wrex
    #
    ve
    cP
    wrex
    #
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    #
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    #
    vx
    cS
    wrex
    #
    cX
    cS
    wcel
    #
    cA
    cQ
    wcel
    cB
    cQ
    wcel
    cC
    cQ
    wcel
    w3a
    #
    cD
    cQ
    wcel
    cE
    cQ
    wcel
    cF
    cQ
    wcel
    w3a
    #
    w3a
    #
    wze
    vp
    cv
    #
    @8
    wceq
    #
    vq
    cv
    #
    @14
    wceq
    #
    wph
    w3a
    #
    vf
    cP
    wrex
    #
    ve
    cP
    wrex
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    vx
    cS
    wrex
    @9
    @31
    wph
    w3a
    #
    vf
    cP
    wrex
    #
    ve
    cP
    wrex
    vd
    cP
    wrex
    #
    vc
    cP
    wrex
    vb
    cP
    wrex
    #
    va
    cP
    wrex
    vx
    cS
    wrex
    @23
    vp
    vq
    @1
    @3
    cR
    cA
    @0
    opex
    cD
    @2
    opex
    @28
    @1
    wceq
    #
    @35
    @39
    vx
    va
    cS
    cP
    @40
    @34
    @38
    vb
    vc
    cP
    cP
    @40
    @33
    @37
    vd
    ve
    cP
    cP
    @40
    @32
    @36
    vf
    cP
    @40
    @29
    @9
    @31
    wph
    @40
    @29
    @1
    @8
    wceq
    @9
    @28
    @1
    @8
    eqeq1
    @1
    @8
    eqcom
    syl6bb
    3anbi1d
    rexbidv
    2rexbidv
    2rexbidv
    2rexbidv
    @30
    @3
    wceq
    #
    @39
    @21
    vx
    va
    cS
    cP
    @41
    @38
    @19
    vb
    vc
    cP
    cP
    @41
    @37
    @17
    vd
    ve
    cP
    cP
    @41
    @36
    @16
    vf
    cP
    @41
    @31
    @15
    @9
    wph
    @41
    @31
    @3
    @14
    wceq
    @15
    @30
    @3
    @14
    eqeq1
    @3
    @14
    eqcom
    syl6bb
    3anbi2d
    rexbidv
    2rexbidv
    2rexbidv
    2rexbidv
    br6.8
    brab
    @27
    @23
    wze
    @27
    @21
    wze
    vx
    va
    cS
    cP
    @27
    vx
    cv
    #
    cS
    wcel
    @4
    cP
    wcel
    wa
    wa
    #
    @19
    wze
    vb
    vc
    cP
    cP
    @43
    @5
    cP
    wcel
    @6
    cP
    wcel
    wa
    wa
    #
    @17
    wze
    vd
    ve
    cP
    cP
    @44
    @10
    cP
    wcel
    @11
    cP
    wcel
    wa
    wa
    #
    @16
    wze
    vf
    cP
    @16
    wze
    wi
    @45
    @12
    cP
    wcel
    wa
    @9
    @15
    wph
    wze
    @9
    wph
    wth
    @15
    wze
    @9
    @4
    cA
    wceq
    #
    @7
    @0
    wceq
    #
    wa
    wph
    wth
    wb
    @4
    @7
    cA
    @0
    va
    vex
    @5
    @6
    opex
    opth
    @46
    wph
    wps
    @47
    wth
    br6.1
    @47
    @5
    cB
    wceq
    #
    @6
    cC
    wceq
    #
    wa
    wps
    wth
    wb
    @5
    @6
    cB
    cC
    vb
    vex
    vc
    vex
    opth
    @48
    wps
    wch
    @49
    wth
    br6.2
    br6.3
    sylan9bb
    sylbi
    sylan9bb
    sylbi
    @15
    @10
    cD
    wceq
    #
    @13
    @2
    wceq
    #
    wa
    wth
    wze
    wb
    @10
    @13
    cD
    @2
    vd
    vex
    @11
    @12
    opex
    opth
    @50
    wth
    wta
    @51
    wze
    br6.4
    @51
    @11
    cE
    wceq
    #
    @12
    cF
    wceq
    #
    wa
    wta
    wze
    wb
    @11
    @12
    cE
    cF
    ve
    vex
    vf
    vex
    opth
    @52
    wta
    wet
    @53
    wze
    br6.5
    br6.6
    sylan9bb
    sylbi
    sylan9bb
    sylbi
    sylan9bb
    biimp3a
    a1i
    rexlimdva
    rexlimdvva
    rexlimdvva
    rexlimdvva
    @27
    wze
    @23
    @27
    wze
    wa
    #
    @24
    @16
    vf
    cQ
    wrex
    #
    ve
    cQ
    wrex
    #
    vd
    cQ
    wrex
    #
    vc
    cQ
    wrex
    #
    vb
    cQ
    wrex
    #
    va
    cQ
    wrex
    #
    @23
    @24
    @25
    @26
    wze
    simpl1
    @54
    @25
    @1
    @1
    wceq
    #
    @15
    wth
    w3a
    #
    vf
    cQ
    wrex
    #
    ve
    cQ
    wrex
    vd
    cQ
    wrex
    #
    @60
    @24
    @25
    @26
    wze
    simpl2
    @26
    @24
    wze
    @64
    @25
    @62
    wze
    @61
    cD
    @13
    cop
    #
    @3
    wceq
    #
    wta
    w3a
    @61
    cD
    cE
    @12
    cop
    #
    cop
    #
    @3
    wceq
    #
    wet
    w3a
    #
    vd
    ve
    vf
    cD
    cE
    cF
    cQ
    cQ
    cQ
    @50
    @15
    @66
    wth
    wta
    @61
    @50
    @14
    @65
    @3
    @10
    cD
    @13
    opeq1
    eqeq1d
    br6.4
    3anbi23d
    @52
    @66
    @69
    wta
    wet
    @61
    @52
    @65
    @68
    @3
    @52
    @13
    @67
    cD
    @11
    cE
    @12
    opeq1
    opeq2d
    eqeq1d
    br6.5
    3anbi23d
    @53
    @70
    @61
    @3
    @3
    wceq
    #
    wze
    w3a
    #
    wze
    @53
    @69
    @71
    wet
    wze
    @61
    @53
    @68
    @3
    @3
    @53
    @67
    @2
    cD
    @12
    cF
    cE
    opeq2
    opeq2d
    eqeq1d
    br6.6
    3anbi23d
    @72
    @61
    @71
    wa
    wze
    @61
    @71
    @1
    eqid
    @3
    eqid
    pm3.2i
    @61
    @71
    wze
    df-3an
    mpbiran
    syl6bb
    rspc3ev
    3ad2antl3
    @57
    @64
    cA
    @7
    cop
    #
    @1
    wceq
    #
    @15
    wps
    w3a
    #
    vf
    cQ
    wrex
    #
    ve
    cQ
    wrex
    vd
    cQ
    wrex
    cA
    cB
    @6
    cop
    #
    cop
    #
    @1
    wceq
    #
    @15
    wch
    w3a
    #
    vf
    cQ
    wrex
    #
    ve
    cQ
    wrex
    vd
    cQ
    wrex
    va
    vb
    vc
    cA
    cB
    cC
    cQ
    cQ
    cQ
    @46
    @55
    @76
    vd
    ve
    cQ
    cQ
    @46
    @16
    @75
    vf
    cQ
    @46
    @9
    @74
    wph
    wps
    @15
    @46
    @8
    @73
    @1
    @4
    cA
    @7
    opeq1
    eqeq1d
    br6.1
    3anbi13d
    rexbidv
    2rexbidv
    @48
    @76
    @81
    vd
    ve
    cQ
    cQ
    @48
    @75
    @80
    vf
    cQ
    @48
    @74
    @79
    wps
    wch
    @15
    @48
    @73
    @78
    @1
    @48
    @7
    @77
    cA
    @5
    cB
    @6
    opeq1
    opeq2d
    eqeq1d
    br6.2
    3anbi13d
    rexbidv
    2rexbidv
    @49
    @81
    @63
    vd
    ve
    cQ
    cQ
    @49
    @80
    @62
    vf
    cQ
    @49
    @79
    @61
    wch
    wth
    @15
    @49
    @78
    @1
    @1
    @49
    @77
    @0
    cA
    @6
    cC
    cB
    opeq2
    opeq2d
    eqeq1d
    br6.3
    3anbi13d
    rexbidv
    2rexbidv
    rspc3ev
    syl2anc
    @22
    @60
    vx
    cX
    cS
    @42
    cX
    wceq
    #
    @21
    @59
    va
    cP
    cQ
    br6.7
    @82
    @20
    @58
    vb
    cP
    cQ
    br6.7
    @82
    @19
    @57
    vc
    cP
    cQ
    br6.7
    @82
    @18
    @56
    vd
    cP
    cQ
    br6.7
    @82
    @17
    @55
    ve
    cP
    cQ
    br6.7
    @82
    @16
    vf
    cP
    cQ
    br6.7
    rexeqdv
    rexeqbidv
    rexeqbidv
    rexeqbidv
    rexeqbidv
    rexeqbidv
    rspcev
    syl2anc
    ex
    impbid
    syl5bb
end
