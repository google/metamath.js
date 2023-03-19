include "cop.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cixp.mm"
include "crab.mm"
include "wa.mm"
include "cfunc.mm"
include "c1st.mm"
include "c2nd.mm"
include "csb.mm"
include "cvv.mm"
include "cmpt2.mm"
include "natfval.mm"
include "a1i.mm"
include "fvexd.mm"
include "simprl.mm"
include "fveq2d.mm"
include "wrel.mm"
include "wbr.mm"
include "relfunc.mm"
include "brrelex12.mm"
include "sylancr.mm"
include "op1stg.mm"
include "syl.mm"
include "adantr.mm"
include "eqtrd.mm"
include "simplrr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "fveq1d.mm"
include "simpr.mm"
include "oveq12d.mm"
include "ixpeq2dv.mm"
include "opeq12d.mm"
include "eqidd.mm"
include "op2ndg.mm"
include "ad3antrrr.mm"
include "oveqd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "rabeqbidv.mm"
include "csbied2.mm"
include "df-br.mm"
include "sylib.mm"
include "ovex.mm"
include "rgenw.mm"
include "ixpexg.mm"
include "ax-mp.mm"
include "rabex.mm"
include "ovmpt2d.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isnat
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  assume natfval.1: |- N = ( C Nat D )
  assume natfval.b: |- B = ( Base ` C )
  assume natfval.h: |- H = ( Hom ` C )
  assume natfval.j: |- J = ( Hom ` D )
  assume natfval.o: |- .x. = ( comp ` D )
  assume isnat.f: |- ( ph -> F ( C Func D ) G )
  assume isnat.g: |- ( ph -> K ( C Func D ) L )

  disjoint h x
  disjoint h y
  disjoint x y
  disjoint A h
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C h
  disjoint C x
  disjoint C y
  disjoint F h
  disjoint F x
  disjoint F y
  disjoint G h
  disjoint G x
  disjoint G y
  disjoint H h
  disjoint h ph
  disjoint ph x
  disjoint ph y
  disjoint K h
  disjoint K x
  disjoint K y
  disjoint L h
  disjoint L x
  disjoint L y
  disjoint D h
  disjoint D x
  disjoint D y
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a x
  disjoint a y
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint f g
  disjoint f h
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint A a
  disjoint B a
  disjoint B f
  disjoint B g
  disjoint B r
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint C a
  disjoint C f
  disjoint C g
  disjoint C r
  disjoint C s
  disjoint C t
  disjoint C u
  disjoint F a
  disjoint F f
  disjoint F g
  disjoint F r
  disjoint F s
  disjoint J a
  disjoint J f
  disjoint J g
  disjoint J r
  disjoint J s
  disjoint J t
  disjoint J u
  disjoint G a
  disjoint G f
  disjoint G g
  disjoint G r
  disjoint G s
  disjoint H a
  disjoint H f
  disjoint H g
  disjoint H r
  disjoint H s
  disjoint H t
  disjoint H u
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint ph r
  disjoint ph s
  disjoint K a
  disjoint K f
  disjoint K g
  disjoint K r
  disjoint K s
  disjoint L a
  disjoint L f
  disjoint L g
  disjoint L r
  disjoint L s
  disjoint .x. a
  disjoint .x. f
  disjoint .x. g
  disjoint .x. r
  disjoint .x. s
  disjoint .x. t
  disjoint .x. u
  disjoint D a
  disjoint D f
  disjoint D g
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  assert |- ( ph -> ( A e. ( <. F , G >. N <. K , L >. ) <-> ( A e. X_ x e. B ( ( F ` x ) J ( K ` x ) ) /\ A. x e. B A. y e. B A. h e. ( x H y ) ( ( A ` y ) ( <. ( F ` x ) , ( F ` y ) >. .x. ( K ` y ) ) ( ( x G y ) ` h ) ) = ( ( ( x L y ) ` h ) ( <. ( F ` x ) , ( K ` x ) >. .x. ( K ` y ) ) ( A ` x ) ) ) ) )

  proof
    wph
    cA
    cF
    cG
    cop
    #
    cK
    cL
    cop
    #
    cN
    co
    #
    wcel
    cA
    vy
    cv
    #
    va
    cv
    #
    cfv
    #
    vh
    cv
    #
    vx
    cv
    #
    @3
    cG
    co
    #
    cfv
    #
    @7
    cF
    cfv
    #
    @3
    cF
    cfv
    #
    cop
    #
    @3
    cK
    cfv
    #
    c.x
    co
    #
    co
    #
    @6
    @7
    @3
    cL
    co
    #
    cfv
    #
    @7
    @4
    cfv
    #
    @10
    @7
    cK
    cfv
    #
    cop
    #
    @13
    c.x
    co
    #
    co
    #
    wceq
    #
    vh
    @7
    @3
    cH
    co
    #
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    va
    vx
    cB
    @10
    @19
    cJ
    co
    #
    cixp
    #
    crab
    #
    wcel
    cA
    @28
    wcel
    @3
    cA
    cfv
    #
    @9
    @14
    co
    #
    @17
    @7
    cA
    cfv
    #
    @21
    co
    #
    wceq
    #
    vh
    @24
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    wph
    @2
    @29
    cA
    wph
    vf
    vg
    @0
    @1
    cC
    cD
    cfunc
    co
    #
    @37
    vr
    vf
    cv
    #
    c1st
    cfv
    #
    vs
    vg
    cv
    #
    c1st
    cfv
    #
    @5
    @6
    @7
    @3
    @38
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @7
    vr
    cv
    #
    cfv
    #
    @3
    @45
    cfv
    #
    cop
    #
    @3
    vs
    cv
    #
    cfv
    #
    c.x
    co
    #
    co
    #
    @6
    @7
    @3
    @40
    c2nd
    cfv
    #
    co
    #
    cfv
    #
    @18
    @46
    @7
    @49
    cfv
    #
    cop
    #
    @50
    c.x
    co
    #
    co
    #
    wceq
    #
    vh
    @24
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    va
    vx
    cB
    @46
    @56
    cJ
    co
    #
    cixp
    #
    crab
    #
    csb
    #
    csb
    #
    @29
    cN
    cvv
    cN
    vf
    vg
    @37
    @37
    @67
    cmpt2
    wceq
    wph
    vx
    vy
    cB
    cC
    cD
    c.x
    vf
    vg
    vh
    cH
    cJ
    cN
    vs
    vr
    va
    natfval.1
    natfval.b
    natfval.h
    natfval.j
    natfval.o
    natfval
    a1i
    wph
    @38
    @0
    wceq
    #
    @40
    @1
    wceq
    #
    wa
    #
    wa
    #
    vr
    @39
    cF
    @66
    @29
    cvv
    @71
    @38
    c1st
    fvexd
    @71
    @39
    @0
    c1st
    cfv
    #
    cF
    @71
    @38
    @0
    c1st
    wph
    @68
    @69
    simprl
    #
    fveq2d
    wph
    @72
    cF
    wceq
    #
    @70
    wph
    cF
    cvv
    wcel
    cG
    cvv
    wcel
    wa
    #
    @74
    wph
    @37
    wrel
    #
    cF
    cG
    @37
    wbr
    #
    @75
    cC
    cD
    relfunc
    #
    isnat.f
    cF
    cG
    @37
    brrelex12
    sylancr
    #
    cF
    cG
    cvv
    cvv
    op1stg
    syl
    adantr
    eqtrd
    @71
    @45
    cF
    wceq
    #
    wa
    #
    vs
    @41
    cK
    @65
    @29
    cvv
    @81
    @40
    c1st
    fvexd
    @81
    @41
    @1
    c1st
    cfv
    #
    cK
    @81
    @40
    @1
    c1st
    wph
    @68
    @69
    @80
    simplrr
    #
    fveq2d
    wph
    @82
    cK
    wceq
    #
    @70
    @80
    wph
    cK
    cvv
    wcel
    cL
    cvv
    wcel
    wa
    #
    @84
    wph
    @76
    cK
    cL
    @37
    wbr
    #
    @85
    @78
    isnat.g
    cK
    cL
    @37
    brrelex12
    sylancr
    #
    cK
    cL
    cvv
    cvv
    op1stg
    syl
    ad2antrr
    eqtrd
    @81
    @49
    cK
    wceq
    #
    wa
    #
    @62
    @26
    va
    @64
    @28
    @89
    vx
    cB
    @63
    @27
    @89
    @46
    @10
    @56
    @19
    cJ
    @89
    @7
    @45
    cF
    @71
    @80
    @88
    simplr
    #
    fveq1d
    #
    @89
    @7
    @49
    cK
    @81
    @88
    simpr
    #
    fveq1d
    #
    oveq12d
    ixpeq2dv
    @89
    @61
    @25
    vx
    vy
    cB
    cB
    @89
    @60
    @23
    vh
    @24
    @89
    @52
    @15
    @59
    @22
    @89
    @5
    @5
    @44
    @9
    @51
    @14
    @89
    @48
    @12
    @50
    @13
    c.x
    @89
    @46
    @10
    @47
    @11
    @91
    @89
    @3
    @45
    cF
    @90
    fveq1d
    opeq12d
    @89
    @3
    @49
    cK
    @92
    fveq1d
    #
    oveq12d
    @89
    @5
    eqidd
    @89
    @6
    @43
    @8
    @89
    @42
    cG
    @7
    @3
    @89
    @42
    @0
    c2nd
    cfv
    #
    cG
    @89
    @38
    @0
    c2nd
    @71
    @68
    @80
    @88
    @73
    ad2antrr
    fveq2d
    wph
    @95
    cG
    wceq
    #
    @70
    @80
    @88
    wph
    @75
    @96
    @79
    cF
    cG
    cvv
    cvv
    op2ndg
    syl
    ad3antrrr
    eqtrd
    oveqd
    fveq1d
    oveq123d
    @89
    @55
    @17
    @18
    @18
    @58
    @21
    @89
    @57
    @20
    @50
    @13
    c.x
    @89
    @46
    @10
    @56
    @19
    @91
    @93
    opeq12d
    @94
    oveq12d
    @89
    @6
    @54
    @16
    @89
    @53
    cL
    @7
    @3
    @89
    @53
    @1
    c2nd
    cfv
    #
    cL
    @89
    @40
    @1
    c2nd
    @81
    @69
    @88
    @83
    adantr
    fveq2d
    wph
    @97
    cL
    wceq
    #
    @70
    @80
    @88
    wph
    @85
    @98
    @87
    cK
    cL
    cvv
    cvv
    op2ndg
    syl
    ad3antrrr
    eqtrd
    oveqd
    fveq1d
    @89
    @18
    eqidd
    oveq123d
    eqeq12d
    ralbidv
    2ralbidv
    rabeqbidv
    csbied2
    csbied2
    wph
    @77
    @0
    @37
    wcel
    isnat.f
    cF
    cG
    @37
    df-br
    sylib
    wph
    @86
    @1
    @37
    wcel
    isnat.g
    cK
    cL
    @37
    df-br
    sylib
    @29
    cvv
    wcel
    wph
    @26
    va
    @28
    @27
    cvv
    wcel
    #
    vx
    cB
    wral
    @28
    cvv
    wcel
    @99
    vx
    cB
    @10
    @19
    cJ
    ovex
    rgenw
    vx
    cB
    @27
    cvv
    ixpexg
    ax-mp
    rabex
    a1i
    ovmpt2d
    eleq2d
    @26
    @36
    va
    cA
    @28
    @4
    cA
    wceq
    #
    @25
    @35
    vx
    vy
    cB
    cB
    @100
    @23
    @34
    vh
    @24
    @100
    @15
    @31
    @22
    @33
    @100
    @5
    @30
    @9
    @14
    @3
    @4
    cA
    fveq1
    oveq1d
    @100
    @18
    @32
    @17
    @21
    @7
    @4
    cA
    fveq1
    oveq2d
    eqeq12d
    ralbidv
    2ralbidv
    elrab
    syl6bb
end
