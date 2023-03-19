include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "cmap.mm"
include "wcel.mm"
include "cxp.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cixp.mm"
include "wa.mm"
include "wceq.mm"
include "cop.mm"
include "wral.mm"
include "copab.mm"
include "wf.mm"
include "w3a.mm"
include "ccat.mm"
include "cbs.mm"
include "chom.mm"
include "ccid.mm"
include "cco.mm"
include "wsbc.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "simplr.mm"
include "feq23d.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "syl6bbr.mm"
include "sqxpeqd.mm"
include "ixpeq1d.mm"
include "oveqd.mm"
include "simpll.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "ixpeq2dv.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "3anbi123d.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "sbcied2.mm"
include "opabbidv.mm"
include "df-func.mm"
include "csn.mm"
include "ciun.mm"
include "ovex.mm"
include "snex.mm"
include "rgenw.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "xpex.mm"
include "iunex.mm"
include "wex.mm"
include "anim2i.mm"
include "2eximi.mm"
include "elopab.mm"
include "eliunxp.mm"
include "3imtr4i.mm"
include "ssriv.mm"
include "ssexi.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"
include "breqd.mm"
include "brabv.mm"
include "elex.mm"
include "anim12i.mm"
include "3adant3.mm"
include "eleq1d.mm"
include "oveq1d.mm"
include "eleq12d.mm"
include "opeq12d.mm"
include "oveq123d.mm"
include "2ralbidv.mm"
include "ralbidv.mm"
include "syl5bbr.mm"
include "eqid.mm"
include "brabga.mm"
include "pm5.21nii.mm"
include "3anbi1i.mm"
include "bitri.mm"

theorem isfunc
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let c.1: class .1.
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cO: class O
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  assume isfunc.b: |- B = ( Base ` D )
  assume isfunc.c: |- C = ( Base ` E )
  assume isfunc.h: |- H = ( Hom ` D )
  assume isfunc.j: |- J = ( Hom ` E )
  assume isfunc.1: |- .1. = ( Id ` D )
  assume isfunc.i: |- I = ( Id ` E )
  assume isfunc.x: |- .x. = ( comp ` D )
  assume isfunc.o: |- O = ( comp ` E )
  assume isfunc.d: |- ( ph -> D e. Cat )
  assume isfunc.e: |- ( ph -> E e. Cat )

  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E m
  disjoint E n
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B d
  disjoint e f
  disjoint e g
  disjoint e m
  disjoint e n
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint C b
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint D b
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D g
  disjoint E b
  disjoint E d
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint H b
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint H g
  disjoint I b
  disjoint I d
  disjoint I e
  disjoint I f
  disjoint I g
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint J b
  disjoint J d
  disjoint J e
  disjoint J f
  disjoint J g
  disjoint .1. b
  disjoint .1. d
  disjoint .1. e
  disjoint .1. f
  disjoint .1. g
  disjoint .x. b
  disjoint .x. d
  disjoint .x. e
  disjoint .x. f
  disjoint .x. g
  disjoint O b
  disjoint O d
  disjoint O e
  disjoint O f
  disjoint O g
  assert |- ( ph -> ( F ( D Func E ) G <-> ( F : B --> C /\ G e. X_ z e. ( B X. B ) ( ( ( F ` ( 1st ` z ) ) J ( F ` ( 2nd ` z ) ) ) ^m ( H ` z ) ) /\ A. x e. B ( ( ( x G x ) ` ( .1. ` x ) ) = ( I ` ( F ` x ) ) /\ A. y e. B A. z e. B A. m e. ( x H y ) A. n e. ( y H z ) ( ( x G z ) ` ( n ( <. x , y >. .x. z ) m ) ) = ( ( ( y G z ) ` n ) ( <. ( F ` x ) , ( F ` y ) >. O ( F ` z ) ) ( ( x G y ) ` m ) ) ) ) ) )

  proof
    wph
    cF
    cG
    cD
    cE
    cfunc
    co
    #
    wbr
    cF
    cG
    vf
    cv
    #
    cC
    cB
    cmap
    co
    #
    wcel
    #
    vg
    cv
    #
    vz
    cB
    cB
    cxp
    #
    vz
    cv
    #
    c1st
    cfv
    #
    @1
    cfv
    #
    @6
    c2nd
    cfv
    #
    @1
    cfv
    #
    cJ
    co
    #
    @6
    cH
    cfv
    #
    cmap
    co
    #
    cixp
    #
    wcel
    #
    wa
    #
    vx
    cv
    #
    c.1
    cfv
    #
    @17
    @17
    @4
    co
    #
    cfv
    #
    @17
    @1
    cfv
    #
    cI
    cfv
    #
    wceq
    #
    vn
    cv
    #
    vm
    cv
    #
    @17
    vy
    cv
    #
    cop
    #
    @6
    c.x
    co
    #
    co
    #
    @17
    @6
    @4
    co
    #
    cfv
    #
    @24
    @26
    @6
    @4
    co
    #
    cfv
    #
    @25
    @17
    @26
    @4
    co
    #
    cfv
    #
    @21
    @26
    @1
    cfv
    #
    cop
    #
    @6
    @1
    cfv
    #
    cO
    co
    #
    co
    #
    wceq
    #
    vn
    @26
    @6
    cH
    co
    #
    wral
    #
    vm
    @17
    @26
    cH
    co
    #
    wral
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    wbr
    #
    cB
    cC
    cF
    wf
    #
    cG
    vz
    @5
    @7
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    cJ
    co
    #
    @12
    cmap
    co
    #
    cixp
    #
    wcel
    #
    @18
    @17
    @17
    cG
    co
    #
    cfv
    #
    @17
    cF
    cfv
    #
    cI
    cfv
    #
    wceq
    #
    @29
    @17
    @6
    cG
    co
    #
    cfv
    #
    @24
    @26
    @6
    cG
    co
    #
    cfv
    #
    @25
    @17
    @26
    cG
    co
    #
    cfv
    #
    @62
    @26
    cF
    cfv
    #
    cop
    #
    @6
    cF
    cfv
    #
    cO
    co
    #
    co
    #
    wceq
    #
    vn
    @42
    wral
    vm
    @44
    wral
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    w3a
    #
    wph
    @0
    @51
    cF
    cG
    wph
    cD
    ccat
    wcel
    cE
    ccat
    wcel
    @0
    @51
    wceq
    isfunc.d
    isfunc.e
    vd
    ve
    cD
    cE
    ccat
    ccat
    vb
    cv
    #
    ve
    cv
    #
    cbs
    cfv
    #
    @1
    wf
    #
    @4
    vz
    @82
    @82
    cxp
    #
    @8
    @10
    @83
    chom
    cfv
    #
    co
    #
    @6
    vd
    cv
    #
    chom
    cfv
    #
    cfv
    #
    cmap
    co
    #
    cixp
    #
    wcel
    #
    @17
    @89
    ccid
    cfv
    #
    cfv
    #
    @19
    cfv
    #
    @21
    @83
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    @24
    @25
    @27
    @6
    @89
    cco
    cfv
    #
    co
    #
    co
    #
    @30
    cfv
    #
    @33
    @35
    @37
    @38
    @83
    cco
    cfv
    #
    co
    #
    co
    #
    wceq
    #
    vn
    @26
    @6
    @90
    co
    #
    wral
    #
    vm
    @17
    @26
    @90
    co
    #
    wral
    #
    vz
    @82
    wral
    #
    vy
    @82
    wral
    #
    wa
    #
    vx
    @82
    wral
    #
    w3a
    #
    vb
    @89
    cbs
    cfv
    #
    wsbc
    #
    vf
    vg
    copab
    @51
    cfunc
    @89
    cD
    wceq
    #
    @83
    cE
    wceq
    #
    wa
    #
    @119
    @50
    vf
    vg
    @122
    @117
    @50
    vb
    @118
    cB
    cvv
    @122
    @89
    cbs
    fvexd
    @122
    @118
    cD
    cbs
    cfv
    #
    cB
    @122
    @89
    cD
    cbs
    @120
    @121
    simpl
    fveq2d
    isfunc.b
    syl6eqr
    @122
    @82
    cB
    wceq
    #
    wa
    #
    @117
    @3
    @15
    @49
    w3a
    #
    @50
    @125
    @85
    @3
    @94
    @15
    @116
    @49
    @125
    @85
    cB
    cC
    @1
    wf
    @3
    @125
    @82
    @84
    cB
    cC
    @1
    @122
    @124
    simpr
    #
    @125
    @84
    cE
    cbs
    cfv
    #
    cC
    @125
    @83
    cE
    cbs
    @120
    @121
    @124
    simplr
    #
    fveq2d
    isfunc.c
    syl6eqr
    feq23d
    cC
    cB
    @1
    cC
    @128
    cvv
    isfunc.c
    cE
    cbs
    fvex
    eqeltri
    #
    cB
    @123
    cvv
    isfunc.b
    cD
    cbs
    fvex
    eqeltri
    #
    elmap
    syl6bbr
    @125
    @93
    @14
    @4
    @125
    @93
    vz
    @5
    @92
    cixp
    @14
    @125
    vz
    @86
    @5
    @92
    @125
    @82
    cB
    @127
    sqxpeqd
    ixpeq1d
    @125
    vz
    @5
    @92
    @13
    @125
    @88
    @11
    @91
    @12
    cmap
    @125
    @87
    cJ
    @8
    @10
    @125
    @87
    cE
    chom
    cfv
    cJ
    @125
    @83
    cE
    chom
    @129
    fveq2d
    isfunc.j
    syl6eqr
    oveqd
    @125
    @6
    @90
    cH
    @125
    @90
    cD
    chom
    cfv
    cH
    @125
    @89
    cD
    chom
    @120
    @121
    @124
    simpll
    #
    fveq2d
    isfunc.h
    syl6eqr
    #
    fveq1d
    oveq12d
    ixpeq2dv
    eqtrd
    eleq2d
    @125
    @115
    @48
    vx
    @82
    cB
    @127
    @125
    @100
    @23
    @114
    @47
    @125
    @97
    @20
    @99
    @22
    @125
    @96
    @18
    @19
    @125
    @17
    @95
    c.1
    @125
    @95
    cD
    ccid
    cfv
    c.1
    @125
    @89
    cD
    ccid
    @132
    fveq2d
    isfunc.1
    syl6eqr
    fveq1d
    fveq2d
    @125
    @21
    @98
    cI
    @125
    @98
    cE
    ccid
    cfv
    cI
    @125
    @83
    cE
    ccid
    @129
    fveq2d
    isfunc.i
    syl6eqr
    fveq1d
    eqeq12d
    @125
    @113
    @46
    vy
    @82
    cB
    @127
    @125
    @112
    @45
    vz
    @82
    cB
    @127
    @125
    @110
    @43
    vm
    @111
    @44
    @125
    @90
    cH
    @17
    @26
    @133
    oveqd
    @125
    @108
    @41
    vn
    @109
    @42
    @125
    @90
    cH
    @26
    @6
    @133
    oveqd
    @125
    @104
    @31
    @107
    @40
    @125
    @103
    @29
    @30
    @125
    @102
    @28
    @24
    @25
    @125
    @101
    c.x
    @27
    @6
    @125
    @101
    cD
    cco
    cfv
    c.x
    @125
    @89
    cD
    cco
    @132
    fveq2d
    isfunc.x
    syl6eqr
    oveqd
    oveqd
    fveq2d
    @125
    @106
    @39
    @33
    @35
    @125
    @105
    cO
    @37
    @38
    @125
    @105
    cE
    cco
    cfv
    cO
    @125
    @83
    cE
    cco
    @129
    fveq2d
    isfunc.o
    syl6eqr
    oveqd
    oveqd
    eqeq12d
    raleqbidv
    raleqbidv
    raleqbidv
    raleqbidv
    anbi12d
    raleqbidv
    3anbi123d
    @3
    @15
    @49
    df-3an
    #
    syl6bb
    sbcied2
    opabbidv
    vx
    vy
    vz
    ve
    vd
    vf
    vg
    vm
    vn
    vb
    df-func
    @51
    vf
    @2
    @1
    csn
    #
    @14
    cxp
    #
    ciun
    #
    vf
    @2
    @136
    cC
    cB
    cmap
    ovex
    @135
    @14
    @1
    snex
    @13
    cvv
    wcel
    #
    vz
    @5
    wral
    @14
    cvv
    wcel
    @138
    vz
    @5
    @11
    @12
    cmap
    ovex
    rgenw
    vz
    @5
    @13
    cvv
    ixpexg
    ax-mp
    xpex
    iunex
    vd
    @51
    @137
    @89
    @1
    @4
    cop
    wceq
    #
    @50
    wa
    #
    vg
    wex
    vf
    wex
    @139
    @16
    wa
    #
    vg
    wex
    vf
    wex
    @89
    @51
    wcel
    @89
    @137
    wcel
    @140
    @141
    vf
    vg
    @50
    @16
    @139
    @16
    @49
    simpl
    anim2i
    2eximi
    @50
    vf
    vg
    @89
    elopab
    vf
    vg
    @2
    @14
    @89
    eliunxp
    3imtr4i
    ssriv
    ssexi
    ovmpt2a
    syl2anc
    breqd
    @52
    cF
    @2
    wcel
    #
    @59
    @80
    w3a
    #
    @81
    @52
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    wa
    #
    @143
    @50
    vf
    vg
    cF
    cG
    brabv
    @142
    @59
    @146
    @80
    @142
    @144
    @59
    @145
    cF
    @2
    elex
    cG
    @58
    elex
    anim12i
    3adant3
    @50
    @143
    vf
    vg
    cF
    cG
    @51
    cvv
    cvv
    @50
    @126
    @1
    cF
    wceq
    #
    @4
    cG
    wceq
    #
    wa
    #
    @143
    @134
    @149
    @3
    @142
    @15
    @59
    @49
    @80
    @149
    @1
    cF
    @2
    @147
    @148
    simpl
    #
    eleq1d
    @149
    @4
    cG
    @14
    @58
    @147
    @148
    simpr
    #
    @149
    vz
    @5
    @13
    @57
    @149
    @11
    @56
    @12
    cmap
    @149
    @8
    @54
    @10
    @55
    cJ
    @149
    @7
    @1
    cF
    @150
    fveq1d
    @149
    @9
    @1
    cF
    @150
    fveq1d
    oveq12d
    oveq1d
    ixpeq2dv
    eleq12d
    @149
    @48
    @79
    vx
    cB
    @149
    @23
    @64
    @47
    @78
    @149
    @20
    @61
    @22
    @63
    @149
    @18
    @19
    @60
    @149
    @4
    cG
    @17
    @17
    @151
    oveqd
    fveq1d
    @149
    @21
    @62
    cI
    @149
    @17
    @1
    cF
    @150
    fveq1d
    #
    fveq2d
    eqeq12d
    @149
    @45
    @77
    vy
    vz
    cB
    cB
    @149
    @41
    @76
    vm
    vn
    @44
    @42
    @149
    @31
    @66
    @40
    @75
    @149
    @29
    @30
    @65
    @149
    @4
    cG
    @17
    @6
    @151
    oveqd
    fveq1d
    @149
    @33
    @68
    @35
    @70
    @39
    @74
    @149
    @37
    @72
    @38
    @73
    cO
    @149
    @21
    @62
    @36
    @71
    @152
    @149
    @26
    @1
    cF
    @150
    fveq1d
    opeq12d
    @149
    @6
    @1
    cF
    @150
    fveq1d
    oveq12d
    @149
    @24
    @32
    @67
    @149
    @4
    cG
    @26
    @6
    @151
    oveqd
    fveq1d
    @149
    @25
    @34
    @69
    @149
    @4
    cG
    @17
    @26
    @151
    oveqd
    fveq1d
    oveq123d
    eqeq12d
    2ralbidv
    2ralbidv
    anbi12d
    ralbidv
    3anbi123d
    syl5bbr
    @51
    eqid
    brabga
    pm5.21nii
    @142
    @53
    @59
    @80
    cC
    cB
    cF
    @130
    @131
    elmap
    3anbi1i
    bitri
    syl6bb
end
