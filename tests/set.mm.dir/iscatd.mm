include "ccat.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "chom.mm"
include "wral.mm"
include "wa.mm"
include "cbs.mm"
include "wrex.mm"
include "wi.mm"
include "3exp2.mm"
include "imp31.mm"
include "ralrimiv.mm"
include "jca.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "w3a.mm"
include "3expia.mm"
include "imp43.mm"
include "3expa.mm"
include "imp32.mm"
include "ex.mm"
include "expr.mm"
include "expd.mm"
include "imp42.mm"
include "ralrimdva.mm"
include "jcad.mm"
include "ralrimivv.mm"
include "ralrimivva.mm"
include "oveqd.mm"
include "raleqbidv.mm"
include "rexeqbidv.mm"
include "eleq12d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "mpbid.mm"
include "wb.mm"
include "eqid.mm"
include "iscat.mm"
include "syl.mm"
include "mpbird.mm"

theorem iscatd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cH: class H
  let cV: class V
  assume iscatd.b: |- ( ph -> B = ( Base ` C ) )
  assume iscatd.h: |- ( ph -> H = ( Hom ` C ) )
  assume iscatd.o: |- ( ph -> .x. = ( comp ` C ) )
  assume iscatd.c: |- ( ph -> C e. V )
  assume iscatd.1: |- ( ( ph /\ x e. B ) -> .1. e. ( x H x ) )
  assume iscatd.2: |- ( ( ph /\ ( x e. B /\ y e. B /\ f e. ( y H x ) ) ) -> ( .1. ( <. y , x >. .x. x ) f ) = f )
  assume iscatd.3: |- ( ( ph /\ ( x e. B /\ y e. B /\ f e. ( x H y ) ) ) -> ( f ( <. x , x >. .x. y ) .1. ) = f )
  assume iscatd.4: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) /\ ( f e. ( x H y ) /\ g e. ( y H z ) ) ) -> ( g ( <. x , y >. .x. z ) f ) e. ( x H z ) )
  assume iscatd.5: |- ( ( ph /\ ( ( x e. B /\ y e. B ) /\ ( z e. B /\ w e. B ) ) /\ ( f e. ( x H y ) /\ g e. ( y H z ) /\ k e. ( z H w ) ) ) -> ( ( k ( <. y , z >. .x. w ) g ) ( <. x , y >. .x. w ) f ) = ( k ( <. x , z >. .x. w ) ( g ( <. x , y >. .x. z ) f ) ) )

  disjoint f g
  disjoint f y
  disjoint .1. f
  disjoint g y
  disjoint .1. g
  disjoint .1. y
  disjoint f k
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint B f
  disjoint g k
  disjoint g w
  disjoint g x
  disjoint g z
  disjoint B g
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint f ph
  disjoint g ph
  disjoint k ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .x. g
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H f
  disjoint H g
  disjoint H k
  disjoint H w
  assert |- ( ph -> C e. Cat )

  proof
    wph
    cC
    ccat
    wcel
    #
    vg
    cv
    #
    vf
    cv
    #
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    @4
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @3
    @4
    cC
    chom
    cfv
    #
    co
    #
    wral
    #
    @2
    @1
    @4
    @4
    cop
    #
    @3
    @6
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @4
    @3
    @10
    co
    #
    wral
    #
    wa
    #
    vy
    cC
    cbs
    cfv
    #
    wral
    #
    vg
    @4
    @4
    @10
    co
    #
    wrex
    #
    @1
    @2
    @4
    @3
    cop
    #
    vz
    cv
    #
    @6
    co
    #
    co
    #
    @4
    @25
    @10
    co
    #
    wcel
    #
    vk
    cv
    #
    @1
    @3
    @25
    cop
    #
    vw
    cv
    #
    @6
    co
    #
    co
    #
    @2
    @24
    @32
    @6
    co
    #
    co
    #
    @30
    @27
    @4
    @25
    cop
    #
    @32
    @6
    co
    #
    co
    #
    wceq
    #
    vk
    @25
    @32
    @10
    co
    #
    wral
    #
    vw
    @20
    wral
    #
    wa
    #
    vg
    @3
    @25
    @10
    co
    #
    wral
    #
    vf
    @17
    wral
    #
    vz
    @20
    wral
    #
    vy
    @20
    wral
    #
    wa
    #
    vx
    @20
    wral
    #
    wph
    @1
    @2
    @5
    @4
    c.x
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @3
    @4
    cH
    co
    #
    wral
    #
    @2
    @1
    @13
    @3
    c.x
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @4
    @3
    cH
    co
    #
    wral
    #
    wa
    #
    vy
    cB
    wral
    #
    vg
    @4
    @4
    cH
    co
    #
    wrex
    #
    @1
    @2
    @24
    @25
    c.x
    co
    #
    co
    #
    @4
    @25
    cH
    co
    #
    wcel
    #
    @30
    @1
    @31
    @32
    c.x
    co
    #
    co
    #
    @2
    @24
    @32
    c.x
    co
    #
    co
    #
    @30
    @67
    @37
    @32
    c.x
    co
    #
    co
    #
    wceq
    #
    vk
    @25
    @32
    cH
    co
    #
    wral
    #
    vw
    cB
    wral
    #
    wa
    #
    vg
    @3
    @25
    cH
    co
    #
    wral
    #
    vf
    @60
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
    @51
    wph
    @86
    vx
    cB
    wph
    @4
    cB
    wcel
    #
    wa
    #
    @65
    @85
    @88
    c.1
    @64
    wcel
    c.1
    @2
    @52
    co
    #
    @2
    wceq
    #
    vf
    @55
    wral
    #
    @2
    c.1
    @57
    co
    #
    @2
    wceq
    #
    vf
    @60
    wral
    #
    wa
    #
    vy
    cB
    wral
    #
    @65
    iscatd.1
    @88
    @95
    vy
    cB
    @88
    @3
    cB
    wcel
    #
    wa
    #
    @91
    @94
    @98
    @90
    vf
    @55
    wph
    @87
    @97
    @2
    @55
    wcel
    #
    @90
    wi
    wph
    @87
    @97
    @99
    @90
    iscatd.2
    3exp2
    imp31
    ralrimiv
    @98
    @93
    vf
    @60
    wph
    @87
    @97
    @2
    @60
    wcel
    #
    @93
    wi
    wph
    @87
    @97
    @100
    @93
    iscatd.3
    3exp2
    imp31
    ralrimiv
    jca
    ralrimiva
    @63
    @96
    vg
    c.1
    @64
    @1
    c.1
    wceq
    #
    @62
    @95
    vy
    cB
    @101
    @56
    @91
    @61
    @94
    @101
    @54
    @90
    vf
    @55
    @101
    @53
    @89
    @2
    @1
    c.1
    @2
    @52
    oveq1
    eqeq1d
    ralbidv
    @101
    @59
    @93
    vf
    @60
    @101
    @58
    @92
    @2
    @1
    c.1
    @2
    @57
    oveq2
    eqeq1d
    ralbidv
    anbi12d
    ralbidv
    rspcev
    syl2anc
    @88
    @83
    vy
    vz
    cB
    cB
    @88
    @97
    @25
    cB
    wcel
    #
    wa
    wa
    #
    @80
    vf
    vg
    @60
    @81
    @103
    @100
    @1
    @81
    wcel
    #
    wa
    #
    @69
    @79
    wph
    @87
    @97
    @102
    @105
    @69
    wi
    #
    wph
    @87
    @97
    @102
    @106
    wph
    @87
    @97
    @102
    w3a
    @105
    @69
    iscatd.4
    3expia
    3exp2
    imp43
    @103
    @105
    @78
    vw
    cB
    @88
    @97
    @102
    @32
    cB
    wcel
    #
    @105
    @78
    wi
    #
    wph
    @87
    @97
    @102
    @107
    @108
    wi
    wi
    wph
    @87
    @97
    wa
    #
    wa
    @102
    @107
    @108
    wph
    @109
    @102
    @107
    wa
    #
    @108
    wph
    @109
    @110
    wa
    #
    wa
    #
    @105
    @78
    @112
    @105
    wa
    @76
    vk
    @77
    @112
    @100
    @104
    @30
    @77
    wcel
    #
    @76
    wi
    @112
    @100
    @104
    @113
    @76
    wph
    @111
    @100
    @104
    @113
    w3a
    @76
    iscatd.5
    3expa
    3exp2
    imp32
    ralrimiv
    ex
    expr
    expd
    expr
    imp42
    ralrimdva
    jcad
    ralrimivv
    ralrimivva
    jca
    ralrimiva
    wph
    @86
    @50
    vx
    cB
    @20
    iscatd.b
    wph
    @65
    @23
    @85
    @49
    wph
    @63
    @21
    vg
    @64
    @22
    wph
    cH
    @10
    @4
    @4
    iscatd.h
    oveqd
    wph
    @62
    @19
    vy
    cB
    @20
    iscatd.b
    wph
    @56
    @12
    @61
    @18
    wph
    @54
    @9
    vf
    @55
    @11
    wph
    cH
    @10
    @3
    @4
    iscatd.h
    oveqd
    wph
    @53
    @8
    @2
    wph
    @52
    @7
    @1
    @2
    wph
    c.x
    @6
    @5
    @4
    iscatd.o
    oveqd
    oveqd
    eqeq1d
    raleqbidv
    wph
    @59
    @16
    vf
    @60
    @17
    wph
    cH
    @10
    @4
    @3
    iscatd.h
    oveqd
    #
    wph
    @58
    @15
    @2
    wph
    @57
    @14
    @2
    @1
    wph
    c.x
    @6
    @13
    @3
    iscatd.o
    oveqd
    oveqd
    eqeq1d
    raleqbidv
    anbi12d
    raleqbidv
    rexeqbidv
    wph
    @84
    @48
    vy
    cB
    @20
    iscatd.b
    wph
    @83
    @47
    vz
    cB
    @20
    iscatd.b
    wph
    @82
    @46
    vf
    @60
    @17
    @114
    wph
    @80
    @44
    vg
    @81
    @45
    wph
    cH
    @10
    @3
    @25
    iscatd.h
    oveqd
    wph
    @69
    @29
    @79
    @43
    wph
    @67
    @27
    @68
    @28
    wph
    @66
    @26
    @1
    @2
    wph
    c.x
    @6
    @24
    @25
    iscatd.o
    oveqd
    oveqd
    #
    wph
    cH
    @10
    @4
    @25
    iscatd.h
    oveqd
    eleq12d
    wph
    @78
    @42
    vw
    cB
    @20
    iscatd.b
    wph
    @76
    @40
    vk
    @77
    @41
    wph
    cH
    @10
    @25
    @32
    iscatd.h
    oveqd
    wph
    @73
    @36
    @75
    @39
    wph
    @71
    @34
    @2
    @2
    @72
    @35
    wph
    c.x
    @6
    @24
    @32
    iscatd.o
    oveqd
    wph
    @70
    @33
    @30
    @1
    wph
    c.x
    @6
    @31
    @32
    iscatd.o
    oveqd
    oveqd
    wph
    @2
    eqidd
    oveq123d
    wph
    @30
    @30
    @67
    @27
    @74
    @38
    wph
    c.x
    @6
    @37
    @32
    iscatd.o
    oveqd
    wph
    @30
    eqidd
    @115
    oveq123d
    eqeq12d
    raleqbidv
    raleqbidv
    anbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    raleqbidv
    anbi12d
    raleqbidv
    mpbid
    wph
    cC
    cV
    wcel
    @0
    @51
    wb
    iscatd.c
    vx
    vy
    vz
    vw
    @20
    cC
    @6
    vf
    vg
    vk
    @10
    cV
    @20
    eqid
    @10
    eqid
    @6
    eqid
    iscat
    syl
    mpbird
end
