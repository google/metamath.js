include "wcel.mm"
include "cnx.mm"
include "citv.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "wrex.mm"
include "crab.mm"
include "cmpt2.mm"
include "cop.mm"
include "csts.mm"
include "clng.mm"
include "w3o.mm"
include "cttg.mm"
include "csb.mm"
include "a1i.mm"
include "cvv.mm"
include "elex.mm"
include "cbs.mm"
include "csg.mm"
include "cvsca.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "rexbidv.mm"
include "rabeqbidv.mm"
include "mpt2eq123dv.mm"
include "csbeq1d.mm"
include "oveq1.mm"
include "rabeq.mm"
include "syl.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "df-ttg.mm"
include "ovex.mm"
include "csbex.mm"
include "fvmpt.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rabbidv.mm"
include "eqeq2d.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "syl6eq.mm"
include "cbvmpt2v.mm"
include "eleq2d.mm"
include "3orbi123d.mm"
include "mpt2eq3dv.mm"
include "syldan.mm"
include "csbied.mm"
include "3eqtrd.mm"
include "fveq2d.mm"
include "itvid.mm"
include "wne.mm"
include "c6.mm"
include "cdc.mm"
include "c7.mm"
include "1nn0.mm"
include "6nn.mm"
include "decnncl.mm"
include "nnrei.mm"
include "6nn0.mm"
include "7nn.mm"
include "6lt7.mm"
include "declt.mm"
include "ltneii.mm"
include "itvndx.mm"
include "lngndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "setsid.mm"
include "mpan2.mm"
include "3eqtr4d.mm"
include "eqtr4d.mm"
include "jca.mm"

theorem ttgval
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.x: class .x.
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cI: class I
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vi: setvar i
  let vw: setvar w
  assume ttgval.n: |- G = ( toTG ` H )
  assume ttgval.b: |- B = ( Base ` H )
  assume ttgval.m: |- .- = ( -g ` H )
  assume ttgval.s: |- .x. = ( .s ` H )
  assume ttgval.i: |- I = ( Itv ` G )

  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint H k
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint .- x
  disjoint .- y
  disjoint .- z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint a b
  disjoint a c
  disjoint a k
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b k
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c k
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint a i
  disjoint a w
  disjoint B a
  disjoint b i
  disjoint b w
  disjoint B b
  disjoint c i
  disjoint c w
  disjoint B c
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint B i
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint i k
  disjoint H i
  disjoint k w
  disjoint H w
  disjoint V i
  disjoint .- a
  disjoint .- b
  disjoint .- c
  disjoint .- i
  disjoint .- w
  disjoint .x. a
  disjoint .x. b
  disjoint .x. c
  disjoint .x. i
  disjoint .x. w
  assert |- ( H e. V -> ( G = ( ( H sSet <. ( Itv ` ndx ) , ( x e. B , y e. B |-> { z e. B | E. k e. ( 0 [,] 1 ) ( z .- x ) = ( k .x. ( y .- x ) ) } ) >. ) sSet <. ( LineG ` ndx ) , ( x e. B , y e. B |-> { z e. B | ( z e. ( x I y ) \/ x e. ( z I y ) \/ y e. ( x I z ) ) } ) >. ) /\ I = ( x e. B , y e. B |-> { z e. B | E. k e. ( 0 [,] 1 ) ( z .- x ) = ( k .x. ( y .- x ) ) } ) ) )

  proof
    cH
    cV
    wcel
    #
    cG
    cH
    cnx
    citv
    cfv
    #
    vx
    vy
    cB
    cB
    vz
    cv
    #
    vx
    cv
    #
    c.mi
    co
    #
    vk
    cv
    #
    vy
    cv
    #
    @3
    c.mi
    co
    #
    c.x
    co
    #
    wceq
    #
    vk
    cc0
    c1
    cicc
    co
    #
    wrex
    #
    vz
    cB
    crab
    #
    cmpt2
    #
    cop
    #
    csts
    co
    #
    cnx
    clng
    cfv
    #
    vx
    vy
    cB
    cB
    @2
    @3
    @6
    cI
    co
    #
    wcel
    #
    @3
    @2
    @6
    cI
    co
    #
    wcel
    #
    @6
    @3
    @2
    cI
    co
    #
    wcel
    #
    w3o
    #
    vz
    cB
    crab
    #
    cmpt2
    #
    cop
    #
    csts
    co
    #
    wceq
    cI
    @13
    wceq
    @0
    cG
    @15
    @16
    vx
    vy
    cB
    cB
    @2
    @3
    @6
    @13
    co
    #
    wcel
    #
    @3
    @2
    @6
    @13
    co
    #
    wcel
    #
    @6
    @3
    @2
    @13
    co
    #
    wcel
    #
    w3o
    #
    vz
    cB
    crab
    #
    cmpt2
    #
    cop
    #
    csts
    co
    #
    @27
    @0
    cG
    cH
    cttg
    cfv
    #
    vi
    @13
    cH
    @1
    vi
    cv
    #
    cop
    #
    csts
    co
    #
    @16
    vx
    vy
    cB
    cB
    @2
    @3
    @6
    @40
    co
    #
    wcel
    #
    @3
    @2
    @6
    @40
    co
    #
    wcel
    #
    @6
    @3
    @2
    @40
    co
    #
    wcel
    #
    w3o
    #
    vz
    cB
    crab
    #
    cmpt2
    #
    cop
    #
    csts
    co
    #
    csb
    #
    @38
    cG
    @39
    wceq
    @0
    ttgval.n
    a1i
    @0
    cH
    cvv
    wcel
    @39
    @54
    wceq
    cH
    cV
    elex
    vw
    cH
    vi
    vx
    vy
    vw
    cv
    #
    cbs
    cfv
    #
    @56
    @2
    @3
    @55
    csg
    cfv
    #
    co
    #
    @5
    @6
    @3
    @57
    co
    #
    @55
    cvsca
    cfv
    #
    co
    #
    wceq
    #
    vk
    @10
    wrex
    #
    vz
    @56
    crab
    #
    cmpt2
    #
    @55
    @41
    csts
    co
    #
    @16
    vx
    vy
    @56
    @56
    @49
    vz
    @56
    crab
    #
    cmpt2
    #
    cop
    #
    csts
    co
    #
    csb
    #
    @54
    cvv
    cttg
    @55
    cH
    wceq
    #
    @71
    vi
    @13
    @70
    csb
    @54
    @72
    vi
    @65
    @13
    @70
    @72
    vx
    vy
    @56
    @56
    @64
    cB
    cB
    @12
    @72
    @56
    cH
    cbs
    cfv
    #
    cB
    @55
    cH
    cbs
    fveq2
    ttgval.b
    syl6eqr
    #
    @74
    @72
    @63
    @11
    vz
    @56
    cB
    @74
    @72
    @62
    @9
    vk
    @10
    @72
    @58
    @4
    @61
    @8
    @72
    @57
    c.mi
    @2
    @3
    @72
    @57
    cH
    csg
    cfv
    c.mi
    @55
    cH
    csg
    fveq2
    ttgval.m
    syl6eqr
    #
    oveqd
    @72
    @5
    @5
    @59
    @7
    @60
    c.x
    @72
    @60
    cH
    cvsca
    cfv
    c.x
    @55
    cH
    cvsca
    fveq2
    ttgval.s
    syl6eqr
    @72
    @5
    eqidd
    @72
    @57
    c.mi
    @6
    @3
    @75
    oveqd
    oveq123d
    eqeq12d
    rexbidv
    rabeqbidv
    mpt2eq123dv
    csbeq1d
    @72
    vi
    @13
    @70
    @53
    @72
    @66
    @42
    @69
    @52
    csts
    @55
    cH
    @41
    csts
    oveq1
    @72
    @68
    @51
    @16
    @72
    vx
    vy
    @56
    @56
    @67
    cB
    cB
    @50
    @74
    @74
    @72
    @56
    cB
    wceq
    @67
    @50
    wceq
    @74
    @49
    vz
    @56
    cB
    rabeq
    syl
    mpt2eq123dv
    opeq2d
    oveq12d
    csbeq2dv
    eqtrd
    vx
    vy
    vz
    vw
    vi
    vk
    df-ttg
    vi
    @13
    @53
    @42
    @52
    csts
    ovex
    csbex
    fvmpt
    syl
    @0
    vi
    @13
    @53
    @38
    cvv
    @13
    cvv
    wcel
    #
    @0
    vx
    vy
    cB
    cB
    @12
    cB
    @73
    cvv
    ttgval.b
    cH
    cbs
    fvex
    eqeltri
    #
    @77
    mpt2ex
    #
    a1i
    @0
    @40
    @13
    wceq
    #
    @40
    va
    vb
    cB
    cB
    vc
    cv
    #
    va
    cv
    #
    c.mi
    co
    #
    @5
    vb
    cv
    #
    @81
    c.mi
    co
    #
    c.x
    co
    #
    wceq
    #
    vk
    @10
    wrex
    #
    vc
    cB
    crab
    #
    cmpt2
    #
    wceq
    #
    @53
    @38
    wceq
    @0
    @79
    wa
    @40
    @13
    @89
    @0
    @79
    simpr
    va
    vb
    vx
    vy
    cB
    cB
    @88
    @12
    @80
    @3
    c.mi
    co
    #
    @5
    @83
    @3
    c.mi
    co
    #
    c.x
    co
    #
    wceq
    #
    vk
    @10
    wrex
    #
    vc
    cB
    crab
    #
    @81
    @3
    wceq
    #
    @87
    @95
    vc
    cB
    @97
    @86
    @94
    vk
    @10
    @97
    @82
    @91
    @85
    @93
    @81
    @3
    @80
    c.mi
    oveq2
    @97
    @84
    @92
    @5
    c.x
    @81
    @3
    @83
    c.mi
    oveq2
    oveq2d
    eqeq12d
    rexbidv
    rabbidv
    @83
    @6
    wceq
    #
    @96
    @91
    @8
    wceq
    #
    vk
    @10
    wrex
    #
    vc
    cB
    crab
    @12
    @98
    @95
    @100
    vc
    cB
    @98
    @94
    @99
    vk
    @10
    @98
    @93
    @8
    @91
    @98
    @92
    @7
    @5
    c.x
    @83
    @6
    @3
    c.mi
    oveq1
    oveq2d
    eqeq2d
    rexbidv
    rabbidv
    @100
    @11
    vc
    vz
    cB
    @80
    @2
    wceq
    #
    @99
    @9
    vk
    @10
    @101
    @91
    @4
    @8
    @80
    @2
    @3
    c.mi
    oveq1
    eqeq1d
    rexbidv
    cbvrabv
    syl6eq
    cbvmpt2v
    #
    syl6eqr
    @0
    @90
    wa
    #
    @42
    @15
    @52
    @37
    csts
    @103
    @41
    @14
    cH
    csts
    @103
    @40
    @13
    @1
    @103
    @40
    @89
    @13
    @0
    @90
    simpr
    @102
    syl6eq
    #
    opeq2d
    oveq2d
    @103
    @51
    @36
    @16
    @103
    vx
    vy
    cB
    cB
    @50
    @35
    @103
    @49
    @34
    vz
    cB
    @103
    @44
    @29
    @46
    @31
    @48
    @33
    @103
    @43
    @28
    @2
    @103
    @40
    @13
    @3
    @6
    @104
    oveqd
    eleq2d
    @103
    @45
    @30
    @3
    @103
    @40
    @13
    @2
    @6
    @104
    oveqd
    eleq2d
    @103
    @47
    @32
    @6
    @103
    @40
    @13
    @3
    @2
    @104
    oveqd
    eleq2d
    3orbi123d
    rabbidv
    mpt2eq3dv
    opeq2d
    oveq12d
    syldan
    csbied
    3eqtrd
    #
    @0
    @26
    @37
    @15
    csts
    @0
    @25
    @36
    @16
    @0
    vx
    vy
    cB
    cB
    @24
    @35
    @0
    @23
    @34
    vz
    cB
    @0
    @18
    @29
    @20
    @31
    @22
    @33
    @0
    @17
    @28
    @2
    @0
    cI
    @13
    @3
    @6
    @0
    cG
    citv
    cfv
    #
    @15
    citv
    cfv
    #
    cI
    @13
    @0
    @106
    @38
    citv
    cfv
    @107
    @0
    cG
    @38
    citv
    @105
    fveq2d
    @36
    @16
    citv
    @15
    itvid
    @1
    @16
    wne
    c1
    c6
    cdc
    #
    c1
    c7
    cdc
    #
    wne
    @108
    @109
    @108
    c1
    c6
    1nn0
    6nn
    decnncl
    nnrei
    c1
    c6
    c7
    1nn0
    6nn0
    7nn
    6lt7
    declt
    ltneii
    @1
    @108
    @16
    @109
    itvndx
    lngndx
    neeq12i
    mpbir
    setsnid
    syl6eqr
    cI
    @106
    wceq
    @0
    ttgval.i
    a1i
    @0
    @76
    @13
    @107
    wceq
    @78
    cV
    @13
    citv
    cvv
    cH
    itvid
    setsid
    mpan2
    3eqtr4d
    #
    oveqd
    eleq2d
    @0
    @19
    @30
    @3
    @0
    cI
    @13
    @2
    @6
    @110
    oveqd
    eleq2d
    @0
    @21
    @32
    @6
    @0
    cI
    @13
    @3
    @2
    @110
    oveqd
    eleq2d
    3orbi123d
    rabbidv
    mpt2eq3dv
    opeq2d
    oveq2d
    eqtr4d
    @110
    jca
end
