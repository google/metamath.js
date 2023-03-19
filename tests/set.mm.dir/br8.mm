include "cop.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wcel.mm"
include "opex.mm"
include "eqeq1.mm"
include "3anbi1d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "3anbi2d.mm"
include "brab.mm"
include "wa.mm"
include "wi.mm"
include "wb.mm"
include "opth.mm"
include "vex.mm"
include "sylan9bb.mm"
include "sylbi.mm"
include "eqcoms.mm"
include "biimp3a.mm"
include "a1i.mm"
include "rexlimdva.mm"
include "rexlimdvva.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpl33.mm"
include "eqidd.mm"
include "simpr.mm"
include "opeq1.mm"
include "opeq2d.mm"
include "eqeq2d.mm"
include "3anbi23d.mm"
include "opeq2.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "3anbi13d.mm"
include "opeq1d.mm"
include "rspc3ev.mm"
include "syl31anc.mm"
include "rexeqdv.mm"
include "rexeqbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem br8
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
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
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume br8.1: |- ( a = A -> ( ph <-> ps ) )
  assume br8.2: |- ( b = B -> ( ps <-> ch ) )
  assume br8.3: |- ( c = C -> ( ch <-> th ) )
  assume br8.4: |- ( d = D -> ( th <-> ta ) )
  assume br8.5: |- ( e = E -> ( ta <-> et ) )
  assume br8.6: |- ( f = F -> ( et <-> ze ) )
  assume br8.7: |- ( g = G -> ( ze <-> si ) )
  assume br8.8: |- ( h = H -> ( si <-> rh ) )
  assume br8.9: |- ( x = X -> P = Q )
  assume br8.10: |- R = { <. p , q >. | E. x e. S E. a e. P E. b e. P E. c e. P E. d e. P E. e e. P E. f e. P E. g e. P E. h e. P ( p = <. <. a , b >. , <. c , d >. >. /\ q = <. <. e , f >. , <. g , h >. >. /\ ph ) }

  disjoint b ch
  disjoint e et
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a p
  disjoint a q
  disjoint P a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b p
  disjoint b q
  disjoint P b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c p
  disjoint c q
  disjoint P c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d p
  disjoint d q
  disjoint P d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e p
  disjoint e q
  disjoint P e
  disjoint f g
  disjoint f h
  disjoint f p
  disjoint f q
  disjoint P f
  disjoint g h
  disjoint g p
  disjoint g q
  disjoint P g
  disjoint h p
  disjoint h q
  disjoint P h
  disjoint p q
  disjoint P p
  disjoint P q
  disjoint a ps
  disjoint g si
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
  disjoint g x
  disjoint A g
  disjoint h x
  disjoint A h
  disjoint p x
  disjoint A p
  disjoint q x
  disjoint A q
  disjoint A x
  disjoint p ph
  disjoint ph q
  disjoint ph x
  disjoint a rh
  disjoint b rh
  disjoint c rh
  disjoint d rh
  disjoint e rh
  disjoint f rh
  disjoint g rh
  disjoint h rh
  disjoint rh x
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B p
  disjoint B q
  disjoint B x
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C p
  disjoint C q
  disjoint C x
  disjoint d ta
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D p
  disjoint D q
  disjoint D x
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E d
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint E h
  disjoint E p
  disjoint E q
  disjoint E x
  disjoint c th
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F p
  disjoint F q
  disjoint F x
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G d
  disjoint G e
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G p
  disjoint G q
  disjoint G x
  disjoint f ze
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint H p
  disjoint H q
  disjoint H x
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S e
  disjoint S f
  disjoint S g
  disjoint S h
  disjoint S p
  disjoint S q
  disjoint S x
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint Q e
  disjoint Q f
  disjoint Q g
  disjoint Q h
  disjoint Q x
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X e
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X x
  assert |- ( ( ( X e. S /\ A e. Q /\ B e. Q ) /\ ( C e. Q /\ D e. Q /\ E e. Q ) /\ ( F e. Q /\ G e. Q /\ H e. Q ) ) -> ( <. <. A , B >. , <. C , D >. >. R <. <. E , F >. , <. G , H >. >. <-> rh ) )

  proof
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cop
    #
    cE
    cF
    cop
    #
    cG
    cH
    cop
    #
    cop
    #
    cR
    wbr
    @2
    va
    cv
    #
    vb
    cv
    #
    cop
    #
    vc
    cv
    #
    vd
    cv
    #
    cop
    #
    cop
    #
    wceq
    #
    @5
    ve
    cv
    #
    vf
    cv
    #
    cop
    #
    vg
    cv
    #
    vh
    cv
    #
    cop
    #
    cop
    #
    wceq
    #
    wph
    w3a
    #
    vh
    cP
    wrex
    #
    vg
    cP
    wrex
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
    #
    cB
    cQ
    wcel
    #
    w3a
    #
    cC
    cQ
    wcel
    #
    cD
    cQ
    wcel
    #
    cE
    cQ
    wcel
    #
    w3a
    #
    cF
    cQ
    wcel
    #
    cG
    cQ
    wcel
    #
    cH
    cQ
    wcel
    #
    w3a
    #
    w3a
    #
    wrh
    vp
    cv
    #
    @12
    wceq
    #
    vq
    cv
    #
    @20
    wceq
    #
    wph
    w3a
    #
    vh
    cP
    wrex
    #
    vg
    cP
    wrex
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
    @13
    @48
    wph
    w3a
    #
    vh
    cP
    wrex
    #
    vg
    cP
    wrex
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
    @31
    vp
    vq
    @2
    @5
    cR
    @0
    @1
    opex
    @3
    @4
    opex
    @45
    @2
    wceq
    #
    @53
    @58
    vx
    va
    cS
    cP
    @59
    @52
    @57
    vb
    vc
    cP
    cP
    @59
    @51
    @56
    vd
    ve
    cP
    cP
    @59
    @50
    @55
    vf
    vg
    cP
    cP
    @59
    @49
    @54
    vh
    cP
    @59
    @46
    @13
    @48
    wph
    @45
    @2
    @12
    eqeq1
    3anbi1d
    rexbidv
    2rexbidv
    2rexbidv
    2rexbidv
    2rexbidv
    @47
    @5
    wceq
    #
    @58
    @29
    vx
    va
    cS
    cP
    @60
    @57
    @27
    vb
    vc
    cP
    cP
    @60
    @56
    @25
    vd
    ve
    cP
    cP
    @60
    @55
    @23
    vf
    vg
    cP
    cP
    @60
    @54
    @22
    vh
    cP
    @60
    @48
    @21
    @13
    wph
    @47
    @5
    @20
    eqeq1
    3anbi2d
    rexbidv
    2rexbidv
    2rexbidv
    2rexbidv
    2rexbidv
    br8.10
    brab
    @44
    @31
    wrh
    @44
    @29
    wrh
    vx
    va
    cS
    cP
    @44
    vx
    cv
    #
    cS
    wcel
    @6
    cP
    wcel
    wa
    wa
    #
    @27
    wrh
    vb
    vc
    cP
    cP
    @62
    @7
    cP
    wcel
    @9
    cP
    wcel
    wa
    wa
    #
    @25
    wrh
    vd
    ve
    cP
    cP
    @63
    @10
    cP
    wcel
    @14
    cP
    wcel
    wa
    wa
    #
    @23
    wrh
    vf
    vg
    cP
    cP
    @64
    @15
    cP
    wcel
    @17
    cP
    wcel
    wa
    wa
    #
    @22
    wrh
    vh
    cP
    @22
    wrh
    wi
    @65
    @18
    cP
    wcel
    wa
    @13
    @21
    wph
    wrh
    @13
    wph
    wta
    @21
    wrh
    wph
    wta
    wb
    #
    @12
    @2
    @12
    @2
    wceq
    @8
    @0
    wceq
    #
    @11
    @1
    wceq
    #
    wa
    @66
    @8
    @11
    @0
    @1
    @6
    @7
    opex
    @9
    @10
    opex
    opth
    @67
    wph
    wch
    @68
    wta
    @67
    @6
    cA
    wceq
    #
    @7
    cB
    wceq
    #
    wa
    wph
    wch
    wb
    @6
    @7
    cA
    cB
    va
    vex
    vb
    vex
    opth
    @69
    wph
    wps
    @70
    wch
    br8.1
    br8.2
    sylan9bb
    sylbi
    @68
    @9
    cC
    wceq
    #
    @10
    cD
    wceq
    #
    wa
    wch
    wta
    wb
    @9
    @10
    cC
    cD
    vc
    vex
    vd
    vex
    opth
    @71
    wch
    wth
    @72
    wta
    br8.3
    br8.4
    sylan9bb
    sylbi
    sylan9bb
    sylbi
    eqcoms
    wta
    wrh
    wb
    #
    @20
    @5
    @20
    @5
    wceq
    @16
    @3
    wceq
    #
    @19
    @4
    wceq
    #
    wa
    @73
    @16
    @19
    @3
    @4
    @14
    @15
    opex
    @17
    @18
    opex
    opth
    @74
    wta
    wze
    @75
    wrh
    @74
    @14
    cE
    wceq
    #
    @15
    cF
    wceq
    #
    wa
    wta
    wze
    wb
    @14
    @15
    cE
    cF
    ve
    vex
    vf
    vex
    opth
    @76
    wta
    wet
    @77
    wze
    br8.5
    br8.6
    sylan9bb
    sylbi
    @75
    @17
    cG
    wceq
    #
    @18
    cH
    wceq
    #
    wa
    wze
    wrh
    wb
    @17
    @18
    cG
    cH
    vg
    vex
    vh
    vex
    opth
    @78
    wze
    wsi
    @79
    wrh
    br8.7
    br8.8
    sylan9bb
    sylbi
    sylan9bb
    sylbi
    eqcoms
    sylan9bb
    biimp3a
    a1i
    rexlimdva
    rexlimdvva
    rexlimdvva
    rexlimdvva
    rexlimdvva
    @44
    wrh
    @31
    @44
    wrh
    wa
    #
    @32
    @22
    vh
    cQ
    wrex
    #
    vg
    cQ
    wrex
    #
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
    @31
    @32
    @33
    @34
    @39
    @43
    wrh
    simpl11
    @80
    @33
    @34
    @36
    @2
    @0
    cC
    @10
    cop
    #
    cop
    #
    wceq
    #
    @21
    wth
    w3a
    #
    vh
    cQ
    wrex
    #
    vg
    cQ
    wrex
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
    @88
    @32
    @33
    @34
    @39
    @43
    wrh
    simpl12
    @32
    @33
    @34
    @39
    @43
    wrh
    simpl13
    @36
    @37
    @38
    @35
    @43
    wrh
    simpl21
    @80
    @37
    @38
    @40
    @2
    @2
    wceq
    #
    @5
    @3
    @19
    cop
    #
    wceq
    #
    wze
    w3a
    #
    vh
    cQ
    wrex
    vg
    cQ
    wrex
    #
    @96
    @36
    @37
    @38
    @35
    @43
    wrh
    simpl22
    @36
    @37
    @38
    @35
    @43
    wrh
    simpl23
    @40
    @41
    @42
    @35
    @39
    wrh
    simpl31
    @80
    @41
    @42
    @97
    @5
    @5
    wceq
    #
    wrh
    @101
    @40
    @41
    @42
    @35
    @39
    wrh
    simpl32
    @40
    @41
    @42
    @35
    @39
    wrh
    simpl33
    @80
    @2
    eqidd
    @80
    @5
    eqidd
    @44
    wrh
    simpr
    @100
    @97
    @102
    wrh
    w3a
    @97
    @5
    @3
    cG
    @18
    cop
    #
    cop
    #
    wceq
    #
    wsi
    w3a
    vg
    vh
    cG
    cH
    cQ
    cQ
    @78
    @99
    @105
    wze
    wsi
    @97
    @78
    @98
    @104
    @5
    @78
    @19
    @103
    @3
    @17
    cG
    @18
    opeq1
    opeq2d
    eqeq2d
    br8.7
    3anbi23d
    @79
    @105
    @102
    wsi
    wrh
    @97
    @79
    @104
    @5
    @5
    @79
    @103
    @4
    @3
    @18
    cH
    cG
    opeq2
    opeq2d
    eqeq2d
    br8.8
    3anbi23d
    rspc2ev
    syl113anc
    @94
    @101
    @97
    @21
    wta
    w3a
    #
    vh
    cQ
    wrex
    vg
    cQ
    wrex
    @97
    @5
    cE
    @15
    cop
    #
    @19
    cop
    #
    wceq
    #
    wet
    w3a
    #
    vh
    cQ
    wrex
    vg
    cQ
    wrex
    vd
    ve
    vf
    cD
    cE
    cF
    cQ
    cQ
    cQ
    @72
    @92
    @106
    vg
    vh
    cQ
    cQ
    @72
    @91
    @97
    wth
    wta
    @21
    @72
    @90
    @2
    @2
    @72
    @89
    @1
    @0
    @10
    cD
    cC
    opeq2
    opeq2d
    eqeq2d
    br8.4
    3anbi13d
    2rexbidv
    @76
    @106
    @110
    vg
    vh
    cQ
    cQ
    @76
    @21
    @109
    wta
    wet
    @97
    @76
    @20
    @108
    @5
    @76
    @16
    @107
    @19
    @14
    cE
    @15
    opeq1
    opeq1d
    eqeq2d
    br8.5
    3anbi23d
    2rexbidv
    @77
    @110
    @100
    vg
    vh
    cQ
    cQ
    @77
    @109
    @99
    wet
    wze
    @97
    @77
    @108
    @98
    @5
    @77
    @107
    @3
    @19
    @15
    cF
    cE
    opeq2
    opeq1d
    eqeq2d
    br8.6
    3anbi23d
    2rexbidv
    rspc3ev
    syl31anc
    @85
    @96
    @2
    cA
    @7
    cop
    #
    @11
    cop
    #
    wceq
    #
    @21
    wps
    w3a
    #
    vh
    cQ
    wrex
    #
    vg
    cQ
    wrex
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
    @2
    @0
    @11
    cop
    #
    wceq
    #
    @21
    wch
    w3a
    #
    vh
    cQ
    wrex
    #
    vg
    cQ
    wrex
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
    @69
    @83
    @116
    vd
    ve
    cQ
    cQ
    @69
    @81
    @115
    vf
    vg
    cQ
    cQ
    @69
    @22
    @114
    vh
    cQ
    @69
    @13
    @113
    wph
    wps
    @21
    @69
    @12
    @112
    @2
    @69
    @8
    @111
    @11
    @6
    cA
    @7
    opeq1
    opeq1d
    eqeq2d
    br8.1
    3anbi13d
    rexbidv
    2rexbidv
    2rexbidv
    @70
    @116
    @121
    vd
    ve
    cQ
    cQ
    @70
    @115
    @120
    vf
    vg
    cQ
    cQ
    @70
    @114
    @119
    vh
    cQ
    @70
    @113
    @118
    wps
    wch
    @21
    @70
    @112
    @117
    @2
    @70
    @111
    @0
    @11
    @7
    cB
    cA
    opeq2
    opeq1d
    eqeq2d
    br8.2
    3anbi13d
    rexbidv
    2rexbidv
    2rexbidv
    @71
    @121
    @95
    vd
    ve
    cQ
    cQ
    @71
    @120
    @93
    vf
    vg
    cQ
    cQ
    @71
    @119
    @92
    vh
    cQ
    @71
    @118
    @91
    wch
    wth
    @21
    @71
    @117
    @90
    @2
    @71
    @11
    @89
    @0
    @9
    cC
    @10
    opeq1
    opeq2d
    eqeq2d
    br8.3
    3anbi13d
    rexbidv
    2rexbidv
    2rexbidv
    rspc3ev
    syl31anc
    @30
    @88
    vx
    cX
    cS
    @61
    cX
    wceq
    #
    @29
    @87
    va
    cP
    cQ
    br8.9
    @122
    @28
    @86
    vb
    cP
    cQ
    br8.9
    @122
    @27
    @85
    vc
    cP
    cQ
    br8.9
    @122
    @26
    @84
    vd
    cP
    cQ
    br8.9
    @122
    @25
    @83
    ve
    cP
    cQ
    br8.9
    @122
    @24
    @82
    vf
    cP
    cQ
    br8.9
    @122
    @23
    @81
    vg
    cP
    cQ
    br8.9
    @122
    @22
    vh
    cP
    cQ
    br8.9
    rexeqdv
    rexeqbidv
    rexeqbidv
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
