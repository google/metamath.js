include "cop.mm"
include "wbr.mm"
include "cv.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "copab.mm"
include "breqd.mm"
include "opex.mm"
include "eqeq1.mm"
include "3anbi1d.mm"
include "rexbidv.mm"
include "2rexbidv.mm"
include "3anbi2d.mm"
include "eqid.mm"
include "brab.mm"
include "syl6bb.mm"
include "wcel.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "opth.mm"
include "vex.mm"
include "sylan9bb.mm"
include "sylbi.mm"
include "eqcoms.mm"
include "biimp3a.mm"
include "a1i.mm"
include "rexlimdva.mm"
include "rexlimdvva.mm"
include "simpl1l.mm"
include "simpl1r.mm"
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
include "ex.mm"
include "impbid.mm"
include "syl233anc.mm"
include "bitrd.mm"

theorem br8d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  assume br8d.1: |- ( a = A -> ( ps <-> ch ) )
  assume br8d.2: |- ( b = B -> ( ch <-> th ) )
  assume br8d.3: |- ( c = C -> ( th <-> ta ) )
  assume br8d.4: |- ( d = D -> ( ta <-> et ) )
  assume br8d.5: |- ( e = E -> ( et <-> ze ) )
  assume br8d.6: |- ( f = F -> ( ze <-> si ) )
  assume br8d.7: |- ( g = G -> ( si <-> rh ) )
  assume br8d.8: |- ( h = H -> ( rh <-> mu ) )
  assume br8d.10: |- ( ph -> R = { <. p , q >. | E. a e. P E. b e. P E. c e. P E. d e. P E. e e. P E. f e. P E. g e. P E. h e. P ( p = <. <. a , b >. , <. c , d >. >. /\ q = <. <. e , f >. , <. g , h >. >. /\ ps ) } )
  assume br8d.11: |- ( ph -> A e. P )
  assume br8d.12: |- ( ph -> B e. P )
  assume br8d.13: |- ( ph -> C e. P )
  assume br8d.14: |- ( ph -> D e. P )
  assume br8d.15: |- ( ph -> E e. P )
  assume br8d.16: |- ( ph -> F e. P )
  assume br8d.17: |- ( ph -> G e. P )
  assume br8d.18: |- ( ph -> H e. P )

  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a p
  disjoint a q
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b p
  disjoint b q
  disjoint A b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c p
  disjoint c q
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d p
  disjoint d q
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e p
  disjoint e q
  disjoint A e
  disjoint f g
  disjoint f h
  disjoint f p
  disjoint f q
  disjoint A f
  disjoint g h
  disjoint g p
  disjoint g q
  disjoint A g
  disjoint h p
  disjoint h q
  disjoint A h
  disjoint p q
  disjoint A p
  disjoint A q
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
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P g
  disjoint P h
  disjoint P p
  disjoint P q
  disjoint a ch
  disjoint b th
  disjoint c ta
  disjoint d et
  disjoint e ze
  disjoint f si
  disjoint g rh
  disjoint p ps
  disjoint ps q
  disjoint a mu
  disjoint b mu
  disjoint c mu
  disjoint d mu
  disjoint e mu
  disjoint f mu
  disjoint g mu
  disjoint h mu
  assert |- ( ph -> ( <. <. A , B >. , <. C , D >. >. R <. <. E , F >. , <. G , H >. >. <-> mu ) )

  proof
    wph
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
    #
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
    wps
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
    #
    wmu
    wph
    @6
    @2
    @5
    vp
    cv
    #
    @13
    wceq
    #
    vq
    cv
    #
    @21
    wceq
    #
    wps
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
    #
    vp
    vq
    copab
    #
    wbr
    @28
    wph
    cR
    @39
    @2
    @5
    br8d.10
    breqd
    @38
    @14
    @32
    wps
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
    @28
    vp
    vq
    @2
    @5
    @39
    @0
    @1
    opex
    @3
    @4
    opex
    @29
    @2
    wceq
    #
    @37
    @44
    va
    cP
    @45
    @36
    @43
    vb
    vc
    cP
    cP
    @45
    @35
    @42
    vd
    ve
    cP
    cP
    @45
    @34
    @41
    vf
    vg
    cP
    cP
    @45
    @33
    @40
    vh
    cP
    @45
    @30
    @14
    @32
    wps
    @29
    @2
    @13
    eqeq1
    3anbi1d
    rexbidv
    2rexbidv
    2rexbidv
    2rexbidv
    rexbidv
    @31
    @5
    wceq
    #
    @44
    @27
    va
    cP
    @46
    @43
    @26
    vb
    vc
    cP
    cP
    @46
    @42
    @25
    vd
    ve
    cP
    cP
    @46
    @41
    @24
    vf
    vg
    cP
    cP
    @46
    @40
    @23
    vh
    cP
    @46
    @32
    @22
    @14
    wps
    @31
    @5
    @21
    eqeq1
    3anbi2d
    rexbidv
    2rexbidv
    2rexbidv
    2rexbidv
    rexbidv
    @39
    eqid
    brab
    syl6bb
    wph
    cA
    cP
    wcel
    #
    cB
    cP
    wcel
    #
    cC
    cP
    wcel
    #
    cD
    cP
    wcel
    #
    cE
    cP
    wcel
    #
    cF
    cP
    wcel
    #
    cG
    cP
    wcel
    #
    cH
    cP
    wcel
    #
    @28
    wmu
    wb
    br8d.11
    br8d.12
    br8d.13
    br8d.14
    br8d.15
    br8d.16
    br8d.17
    br8d.18
    @47
    @48
    wa
    #
    @49
    @50
    @51
    w3a
    #
    @52
    @53
    @54
    w3a
    #
    w3a
    #
    @28
    wmu
    @58
    @27
    wmu
    va
    cP
    @58
    @7
    cP
    wcel
    wa
    #
    @26
    wmu
    vb
    vc
    cP
    cP
    @59
    @8
    cP
    wcel
    @10
    cP
    wcel
    wa
    wa
    #
    @25
    wmu
    vd
    ve
    cP
    cP
    @60
    @11
    cP
    wcel
    @15
    cP
    wcel
    wa
    wa
    #
    @24
    wmu
    vf
    vg
    cP
    cP
    @61
    @16
    cP
    wcel
    @18
    cP
    wcel
    wa
    wa
    #
    @23
    wmu
    vh
    cP
    @23
    wmu
    wi
    @62
    @19
    cP
    wcel
    wa
    @14
    @22
    wps
    wmu
    @14
    wps
    wet
    @22
    wmu
    wps
    wet
    wb
    #
    @13
    @2
    @13
    @2
    wceq
    @9
    @0
    wceq
    #
    @12
    @1
    wceq
    #
    wa
    @63
    @9
    @12
    @0
    @1
    @7
    @8
    opex
    @10
    @11
    opex
    opth
    @64
    wps
    wth
    @65
    wet
    @64
    @7
    cA
    wceq
    #
    @8
    cB
    wceq
    #
    wa
    wps
    wth
    wb
    @7
    @8
    cA
    cB
    va
    vex
    vb
    vex
    opth
    @66
    wps
    wch
    @67
    wth
    br8d.1
    br8d.2
    sylan9bb
    sylbi
    @65
    @10
    cC
    wceq
    #
    @11
    cD
    wceq
    #
    wa
    wth
    wet
    wb
    @10
    @11
    cC
    cD
    vc
    vex
    vd
    vex
    opth
    @68
    wth
    wta
    @69
    wet
    br8d.3
    br8d.4
    sylan9bb
    sylbi
    sylan9bb
    sylbi
    eqcoms
    wet
    wmu
    wb
    #
    @21
    @5
    @21
    @5
    wceq
    @17
    @3
    wceq
    #
    @20
    @4
    wceq
    #
    wa
    @70
    @17
    @20
    @3
    @4
    @15
    @16
    opex
    @18
    @19
    opex
    opth
    @71
    wet
    wsi
    @72
    wmu
    @71
    @15
    cE
    wceq
    #
    @16
    cF
    wceq
    #
    wa
    wet
    wsi
    wb
    @15
    @16
    cE
    cF
    ve
    vex
    vf
    vex
    opth
    @73
    wet
    wze
    @74
    wsi
    br8d.5
    br8d.6
    sylan9bb
    sylbi
    @72
    @18
    cG
    wceq
    #
    @19
    cH
    wceq
    #
    wa
    wsi
    wmu
    wb
    @18
    @19
    cG
    cH
    vg
    vex
    vh
    vex
    opth
    @75
    wsi
    wrh
    @76
    wmu
    br8d.7
    br8d.8
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
    rexlimdva
    @58
    wmu
    @28
    @58
    wmu
    wa
    #
    @47
    @48
    @49
    @2
    @0
    cC
    @11
    cop
    #
    cop
    #
    wceq
    #
    @22
    wta
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
    vd
    cP
    wrex
    #
    @28
    @47
    @48
    @56
    @57
    wmu
    simpl1l
    @47
    @48
    @56
    @57
    wmu
    simpl1r
    @49
    @50
    @51
    @55
    @57
    wmu
    simpl21
    @77
    @50
    @51
    @52
    @2
    @2
    wceq
    #
    @5
    @3
    @20
    cop
    #
    wceq
    #
    wsi
    w3a
    #
    vh
    cP
    wrex
    vg
    cP
    wrex
    #
    @85
    @49
    @50
    @51
    @55
    @57
    wmu
    simpl22
    @49
    @50
    @51
    @55
    @57
    wmu
    simpl23
    @52
    @53
    @54
    @55
    @56
    wmu
    simpl31
    @77
    @53
    @54
    @86
    @5
    @5
    wceq
    #
    wmu
    @90
    @52
    @53
    @54
    @55
    @56
    wmu
    simpl32
    @52
    @53
    @54
    @55
    @56
    wmu
    simpl33
    @77
    @2
    eqidd
    @77
    @5
    eqidd
    @58
    wmu
    simpr
    @89
    @86
    @91
    wmu
    w3a
    @86
    @5
    @3
    cG
    @19
    cop
    #
    cop
    #
    wceq
    #
    wrh
    w3a
    vg
    vh
    cG
    cH
    cP
    cP
    @75
    @88
    @94
    wsi
    wrh
    @86
    @75
    @87
    @93
    @5
    @75
    @20
    @92
    @3
    @18
    cG
    @19
    opeq1
    opeq2d
    eqeq2d
    br8d.7
    3anbi23d
    @76
    @94
    @91
    wrh
    wmu
    @86
    @76
    @93
    @5
    @5
    @76
    @92
    @4
    @3
    @19
    cH
    cG
    opeq2
    opeq2d
    eqeq2d
    br8d.8
    3anbi23d
    rspc2ev
    syl113anc
    @83
    @90
    @86
    @22
    wet
    w3a
    #
    vh
    cP
    wrex
    vg
    cP
    wrex
    @86
    @5
    cE
    @16
    cop
    #
    @20
    cop
    #
    wceq
    #
    wze
    w3a
    #
    vh
    cP
    wrex
    vg
    cP
    wrex
    vd
    ve
    vf
    cD
    cE
    cF
    cP
    cP
    cP
    @69
    @81
    @95
    vg
    vh
    cP
    cP
    @69
    @80
    @86
    wta
    wet
    @22
    @69
    @79
    @2
    @2
    @69
    @78
    @1
    @0
    @11
    cD
    cC
    opeq2
    opeq2d
    eqeq2d
    br8d.4
    3anbi13d
    2rexbidv
    @73
    @95
    @99
    vg
    vh
    cP
    cP
    @73
    @22
    @98
    wet
    wze
    @86
    @73
    @21
    @97
    @5
    @73
    @17
    @96
    @20
    @15
    cE
    @16
    opeq1
    opeq1d
    eqeq2d
    br8d.5
    3anbi23d
    2rexbidv
    @74
    @99
    @89
    vg
    vh
    cP
    cP
    @74
    @98
    @88
    wze
    wsi
    @86
    @74
    @97
    @87
    @5
    @74
    @96
    @3
    @20
    @16
    cF
    cE
    opeq2
    opeq1d
    eqeq2d
    br8d.6
    3anbi23d
    2rexbidv
    rspc3ev
    syl31anc
    @26
    @85
    @2
    cA
    @8
    cop
    #
    @12
    cop
    #
    wceq
    #
    @22
    wch
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
    @2
    @0
    @12
    cop
    #
    wceq
    #
    @22
    wth
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
    va
    vb
    vc
    cA
    cB
    cC
    cP
    cP
    cP
    @66
    @25
    @105
    vd
    ve
    cP
    cP
    @66
    @24
    @104
    vf
    vg
    cP
    cP
    @66
    @23
    @103
    vh
    cP
    @66
    @14
    @102
    wps
    wch
    @22
    @66
    @13
    @101
    @2
    @66
    @9
    @100
    @12
    @7
    cA
    @8
    opeq1
    opeq1d
    eqeq2d
    br8d.1
    3anbi13d
    rexbidv
    2rexbidv
    2rexbidv
    @67
    @105
    @110
    vd
    ve
    cP
    cP
    @67
    @104
    @109
    vf
    vg
    cP
    cP
    @67
    @103
    @108
    vh
    cP
    @67
    @102
    @107
    wch
    wth
    @22
    @67
    @101
    @106
    @2
    @67
    @100
    @0
    @12
    @8
    cB
    cA
    opeq2
    opeq1d
    eqeq2d
    br8d.2
    3anbi13d
    rexbidv
    2rexbidv
    2rexbidv
    @68
    @110
    @84
    vd
    ve
    cP
    cP
    @68
    @109
    @82
    vf
    vg
    cP
    cP
    @68
    @108
    @81
    vh
    cP
    @68
    @107
    @80
    wth
    wta
    @22
    @68
    @106
    @79
    @2
    @68
    @12
    @78
    @0
    @10
    cC
    @11
    opeq1
    opeq2d
    eqeq2d
    br8d.3
    3anbi13d
    rexbidv
    2rexbidv
    2rexbidv
    rspc3ev
    syl31anc
    ex
    impbid
    syl233anc
    bitrd
end
