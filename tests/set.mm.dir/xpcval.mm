include "cxpc.mm"
include "co.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "cvv.mm"
include "cv.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "csb.mm"
include "wceq.mm"
include "df-xpc.mm"
include "a1i.mm"
include "wa.mm"
include "wcel.mm"
include "fvex.mm"
include "xpex.mm"
include "simprl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "simprr.mm"
include "xpeq12d.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "vex.mm"
include "mpt2ex.mm"
include "simpr.mm"
include "simplrl.mm"
include "oveqd.mm"
include "simplrr.mm"
include "mpt2eq123dv.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "opeq2d.mm"
include "fveq1d.mm"
include "opeq12d.mm"
include "ad3antrrr.mm"
include "tpeq123d.mm"
include "csbied2.mm"
include "elex.mm"
include "syl.mm"
include "tpex.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem xpcval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cD: class D
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cJ: class J
  let cK: class K
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  assume xpcval.t: |- T = ( C Xc. D )
  assume xpcval.x: |- X = ( Base ` C )
  assume xpcval.y: |- Y = ( Base ` D )
  assume xpcval.h: |- H = ( Hom ` C )
  assume xpcval.j: |- J = ( Hom ` D )
  assume xpcval.o1: |- .x. = ( comp ` C )
  assume xpcval.o2: |- .xb = ( comp ` D )
  assume xpcval.c: |- ( ph -> C e. V )
  assume xpcval.d: |- ( ph -> D e. W )
  assume xpcval.b: |- ( ph -> B = ( X X. Y ) )
  assume xpcval.k: |- ( ph -> K = ( u e. B , v e. B |-> ( ( ( 1st ` u ) H ( 1st ` v ) ) X. ( ( 2nd ` u ) J ( 2nd ` v ) ) ) ) )
  assume xpcval.o: |- ( ph -> O = ( x e. ( B X. B ) , y e. B |-> ( g e. ( ( 2nd ` x ) K y ) , f e. ( K ` x ) |-> <. ( ( 1st ` g ) ( <. ( 1st ` ( 1st ` x ) ) , ( 1st ` ( 2nd ` x ) ) >. .x. ( 1st ` y ) ) ( 1st ` f ) ) , ( ( 2nd ` g ) ( <. ( 2nd ` ( 1st ` x ) ) , ( 2nd ` ( 2nd ` x ) ) >. .xb ( 2nd ` y ) ) ( 2nd ` f ) ) >. ) ) )

  disjoint f g
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint f ph
  disjoint g ph
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint C f
  disjoint C g
  disjoint C u
  disjoint C v
  disjoint C x
  disjoint C y
  disjoint D f
  disjoint D g
  disjoint D u
  disjoint D v
  disjoint D x
  disjoint D y
  disjoint K f
  disjoint K g
  disjoint K x
  disjoint K y
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint f h
  disjoint f r
  disjoint f s
  disjoint g h
  disjoint g r
  disjoint g s
  disjoint h r
  disjoint h s
  disjoint h u
  disjoint h v
  disjoint h x
  disjoint h y
  disjoint B h
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint B r
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint B s
  disjoint O b
  disjoint O h
  disjoint O r
  disjoint O s
  disjoint b ph
  disjoint h ph
  disjoint ph r
  disjoint ph s
  disjoint C b
  disjoint C h
  disjoint C r
  disjoint C s
  disjoint D b
  disjoint D h
  disjoint D r
  disjoint D s
  disjoint K b
  disjoint K h
  disjoint K r
  disjoint K s
  assert |- ( ph -> T = { <. ( Base ` ndx ) , B >. , <. ( Hom ` ndx ) , K >. , <. ( comp ` ndx ) , O >. } )

  proof
    wph
    cT
    cC
    cD
    cxpc
    co
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    chom
    cfv
    #
    cK
    cop
    #
    cnx
    cco
    cfv
    #
    cO
    cop
    #
    ctp
    #
    xpcval.t
    wph
    vr
    vs
    cC
    cD
    cvv
    cvv
    vb
    vr
    cv
    #
    cbs
    cfv
    #
    vs
    cv
    #
    cbs
    cfv
    #
    cxp
    #
    vh
    vu
    vv
    vb
    cv
    #
    @12
    vu
    cv
    #
    c1st
    cfv
    #
    vv
    cv
    #
    c1st
    cfv
    #
    @7
    chom
    cfv
    #
    co
    #
    @13
    c2nd
    cfv
    #
    @15
    c2nd
    cfv
    #
    @9
    chom
    cfv
    #
    co
    #
    cxp
    #
    cmpt2
    #
    @0
    @12
    cop
    #
    @2
    vh
    cv
    #
    cop
    #
    @4
    vx
    vy
    @12
    @12
    cxp
    #
    @12
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    @26
    co
    #
    @29
    @26
    cfv
    #
    vg
    cv
    #
    c1st
    cfv
    #
    vf
    cv
    #
    c1st
    cfv
    #
    @29
    c1st
    cfv
    #
    c1st
    cfv
    @30
    c1st
    cfv
    cop
    #
    @31
    c1st
    cfv
    #
    @7
    cco
    cfv
    #
    co
    #
    co
    #
    @34
    c2nd
    cfv
    #
    @36
    c2nd
    cfv
    #
    @38
    c2nd
    cfv
    @30
    c2nd
    cfv
    cop
    #
    @31
    c2nd
    cfv
    #
    @9
    cco
    cfv
    #
    co
    #
    co
    #
    cop
    #
    cmpt2
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    csb
    #
    csb
    #
    @6
    cxpc
    cvv
    cxpc
    vr
    vs
    cvv
    cvv
    @57
    cmpt2
    wceq
    wph
    vx
    vy
    vv
    vu
    vf
    vg
    vh
    vs
    vr
    vb
    df-xpc
    a1i
    wph
    @7
    cC
    wceq
    #
    @9
    cD
    wceq
    #
    wa
    #
    wa
    #
    vb
    @11
    cB
    @56
    @6
    cvv
    @11
    cvv
    wcel
    @61
    @8
    @10
    @7
    cbs
    fvex
    @9
    cbs
    fvex
    xpex
    a1i
    @61
    @11
    cX
    cY
    cxp
    #
    cB
    @61
    @8
    cX
    @10
    cY
    @61
    @8
    cC
    cbs
    cfv
    cX
    @61
    @7
    cC
    cbs
    wph
    @58
    @59
    simprl
    fveq2d
    xpcval.x
    syl6eqr
    @61
    @10
    cD
    cbs
    cfv
    cY
    @61
    @9
    cD
    cbs
    wph
    @58
    @59
    simprr
    fveq2d
    xpcval.y
    syl6eqr
    xpeq12d
    wph
    cB
    @62
    wceq
    @60
    xpcval.b
    adantr
    eqtr4d
    @61
    @12
    cB
    wceq
    #
    wa
    #
    vh
    @24
    cK
    @55
    @6
    cvv
    @24
    cvv
    wcel
    @64
    vu
    vv
    @12
    @12
    @23
    vb
    vex
    #
    @65
    mpt2ex
    a1i
    @64
    @24
    vu
    vv
    cB
    cB
    @14
    @16
    cH
    co
    #
    @19
    @20
    cJ
    co
    #
    cxp
    #
    cmpt2
    #
    cK
    @64
    vu
    vv
    @12
    @12
    @23
    cB
    cB
    @68
    @61
    @63
    simpr
    #
    @70
    @64
    @18
    @66
    @22
    @67
    @64
    @17
    cH
    @14
    @16
    @64
    @17
    cC
    chom
    cfv
    cH
    @64
    @7
    cC
    chom
    wph
    @58
    @59
    @63
    simplrl
    #
    fveq2d
    xpcval.h
    syl6eqr
    oveqd
    @64
    @21
    cJ
    @19
    @20
    @64
    @21
    cD
    chom
    cfv
    cJ
    @64
    @9
    cD
    chom
    wph
    @58
    @59
    @63
    simplrr
    #
    fveq2d
    xpcval.j
    syl6eqr
    oveqd
    xpeq12d
    mpt2eq123dv
    wph
    cK
    @69
    wceq
    @60
    @63
    xpcval.k
    ad2antrr
    eqtr4d
    @64
    @26
    cK
    wceq
    #
    wa
    #
    @25
    @1
    @27
    @3
    @54
    @5
    @74
    @12
    cB
    @0
    @61
    @63
    @73
    simplr
    #
    opeq2d
    @74
    @26
    cK
    @2
    @64
    @73
    simpr
    #
    opeq2d
    @74
    @53
    cO
    @4
    @74
    @53
    vx
    vy
    cB
    cB
    cxp
    #
    cB
    vg
    vf
    @30
    @31
    cK
    co
    #
    @29
    cK
    cfv
    #
    @35
    @37
    @39
    @40
    c.x
    co
    #
    co
    #
    @44
    @45
    @46
    @47
    c.xb
    co
    #
    co
    #
    cop
    #
    cmpt2
    #
    cmpt2
    #
    cO
    @74
    vx
    vy
    @28
    @12
    @52
    @77
    cB
    @85
    @74
    @12
    cB
    @12
    cB
    @75
    @75
    xpeq12d
    @75
    @74
    vg
    vf
    @32
    @33
    @51
    @78
    @79
    @84
    @74
    @26
    cK
    @30
    @31
    @76
    oveqd
    @74
    @29
    @26
    cK
    @76
    fveq1d
    @74
    @43
    @81
    @50
    @83
    @74
    @42
    @80
    @35
    @37
    @74
    @41
    c.x
    @39
    @40
    @74
    @41
    cC
    cco
    cfv
    c.x
    @74
    @7
    cC
    cco
    @64
    @58
    @73
    @71
    adantr
    fveq2d
    xpcval.o1
    syl6eqr
    oveqd
    oveqd
    @74
    @49
    @82
    @44
    @45
    @74
    @48
    c.xb
    @46
    @47
    @74
    @48
    cD
    cco
    cfv
    c.xb
    @74
    @9
    cD
    cco
    @64
    @59
    @73
    @72
    adantr
    fveq2d
    xpcval.o2
    syl6eqr
    oveqd
    oveqd
    opeq12d
    mpt2eq123dv
    mpt2eq123dv
    wph
    cO
    @86
    wceq
    @60
    @63
    @73
    xpcval.o
    ad3antrrr
    eqtr4d
    opeq2d
    tpeq123d
    csbied2
    csbied2
    wph
    cC
    cV
    wcel
    cC
    cvv
    wcel
    xpcval.c
    cC
    cV
    elex
    syl
    wph
    cD
    cW
    wcel
    cD
    cvv
    wcel
    xpcval.d
    cD
    cW
    elex
    syl
    @6
    cvv
    wcel
    wph
    @1
    @3
    @5
    tpex
    a1i
    ovmpt2d
    syl5eq
end
