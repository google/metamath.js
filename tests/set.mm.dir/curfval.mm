include "cop.mm"
include "ccurf.mm"
include "co.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cmpt.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cvv.mm"
include "cbs.mm"
include "chom.mm"
include "ccid.mm"
include "csb.mm"
include "wceq.mm"
include "df-curf.mm"
include "a1i.mm"
include "wa.mm"
include "fvexd.mm"
include "simprl.mm"
include "fveq2d.mm"
include "ccat.mm"
include "wcel.mm"
include "op1stg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eqtrd.mm"
include "op2ndg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "syl6eqr.mm"
include "simpr.mm"
include "simprr.mm"
include "oveqd.mm"
include "mpteq12dv.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpt2eq123dv.mm"
include "opeq12d.mm"
include "csbied2.mm"
include "opex.mm"
include "cxpc.mm"
include "cfunc.mm"
include "elex.mm"
include "syl.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem curfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.1: class .1.
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vh: setvar h
  let vw: setvar w
  let cY: class Y
  let cZ: class Z
  let cK: class K
  let cX: class X
  assume curfval.g: |- G = ( <. C , D >. curryF F )
  assume curfval.a: |- A = ( Base ` C )
  assume curfval.c: |- ( ph -> C e. Cat )
  assume curfval.d: |- ( ph -> D e. Cat )
  assume curfval.f: |- ( ph -> F e. ( ( C Xc. D ) Func E ) )
  assume curfval.b: |- B = ( Base ` D )
  assume curfval.j: |- J = ( Hom ` D )
  assume curfval.1: |- .1. = ( Id ` C )
  assume curfval.h: |- H = ( Hom ` C )
  assume curfval.i: |- I = ( Id ` D )

  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .1. g
  disjoint x y
  disjoint x z
  disjoint .1. x
  disjoint y z
  disjoint .1. y
  disjoint .1. z
  disjoint A x
  disjoint A y
  disjoint B g
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint H g
  disjoint H y
  disjoint H z
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint E g
  disjoint E y
  disjoint E z
  disjoint J g
  disjoint J x
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .1. c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint .1. d
  disjoint e f
  disjoint e g
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint .1. e
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint .1. f
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint c h
  disjoint c w
  disjoint B c
  disjoint d h
  disjoint d w
  disjoint B d
  disjoint e h
  disjoint e w
  disjoint B e
  disjoint f h
  disjoint f w
  disjoint B f
  disjoint g h
  disjoint g w
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint B h
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D h
  disjoint D w
  disjoint H c
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint I c
  disjoint I d
  disjoint I e
  disjoint I f
  disjoint c ph
  disjoint d ph
  disjoint e ph
  disjoint f ph
  disjoint h ph
  disjoint ph w
  disjoint Y g
  disjoint Y y
  disjoint Y z
  disjoint Z g
  disjoint Z y
  disjoint Z z
  disjoint E h
  disjoint E w
  disjoint J c
  disjoint J d
  disjoint J e
  disjoint J f
  disjoint K g
  disjoint K h
  disjoint K w
  disjoint K y
  disjoint K z
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  assert |- ( ph -> G = <. ( x e. A |-> <. ( y e. B |-> ( x ( 1st ` F ) y ) ) , ( y e. B , z e. B |-> ( g e. ( y J z ) |-> ( ( .1. ` x ) ( <. x , y >. ( 2nd ` F ) <. x , z >. ) g ) ) ) >. ) , ( x e. A , y e. A |-> ( g e. ( x H y ) |-> ( z e. B |-> ( g ( <. x , z >. ( 2nd ` F ) <. y , z >. ) ( I ` z ) ) ) ) ) >. )

  proof
    wph
    cG
    cC
    cD
    cop
    #
    cF
    ccurf
    co
    vx
    cA
    vy
    cB
    vx
    cv
    #
    vy
    cv
    #
    cF
    c1st
    cfv
    #
    co
    #
    cmpt
    #
    vy
    vz
    cB
    cB
    vg
    @2
    vz
    cv
    #
    cJ
    co
    #
    @1
    c.1
    cfv
    #
    vg
    cv
    #
    @1
    @2
    cop
    #
    @1
    @6
    cop
    #
    cF
    c2nd
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    cmpt
    #
    vx
    vy
    cA
    cA
    vg
    @1
    @2
    cH
    co
    #
    vz
    cB
    @9
    @6
    cI
    cfv
    #
    @11
    @2
    @6
    cop
    #
    @12
    co
    #
    co
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    curfval.g
    wph
    ve
    vf
    @0
    cF
    cvv
    cvv
    vc
    ve
    cv
    #
    c1st
    cfv
    #
    vd
    @28
    c2nd
    cfv
    #
    vx
    vc
    cv
    #
    cbs
    cfv
    #
    vy
    vd
    cv
    #
    cbs
    cfv
    #
    @1
    @2
    vf
    cv
    #
    c1st
    cfv
    #
    co
    #
    cmpt
    #
    vy
    vz
    @34
    @34
    vg
    @2
    @6
    @33
    chom
    cfv
    #
    co
    #
    @1
    @31
    ccid
    cfv
    #
    cfv
    #
    @9
    @10
    @11
    @35
    c2nd
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    cmpt
    #
    vx
    vy
    @32
    @32
    vg
    @1
    @2
    @31
    chom
    cfv
    #
    co
    #
    vz
    @34
    @9
    @6
    @33
    ccid
    cfv
    #
    cfv
    #
    @11
    @21
    @43
    co
    #
    co
    #
    cmpt
    #
    cmpt
    #
    cmpt2
    #
    cop
    #
    csb
    #
    csb
    #
    @27
    ccurf
    cvv
    ccurf
    ve
    vf
    cvv
    cvv
    @61
    cmpt2
    wceq
    wph
    vx
    vy
    vz
    ve
    vf
    vg
    vc
    vd
    df-curf
    a1i
    wph
    @28
    @0
    wceq
    #
    @35
    cF
    wceq
    #
    wa
    #
    wa
    #
    vc
    @29
    cC
    @60
    @27
    cvv
    @65
    @28
    c1st
    fvexd
    @65
    @29
    @0
    c1st
    cfv
    #
    cC
    @65
    @28
    @0
    c1st
    wph
    @62
    @63
    simprl
    #
    fveq2d
    wph
    @66
    cC
    wceq
    #
    @64
    wph
    cC
    ccat
    wcel
    #
    cD
    ccat
    wcel
    #
    @68
    curfval.c
    curfval.d
    cC
    cD
    ccat
    ccat
    op1stg
    syl2anc
    adantr
    eqtrd
    @65
    @31
    cC
    wceq
    #
    wa
    #
    vd
    @30
    cD
    @59
    @27
    cvv
    @72
    @28
    c2nd
    fvexd
    @72
    @30
    @0
    c2nd
    cfv
    #
    cD
    @72
    @28
    @0
    c2nd
    @65
    @62
    @71
    @67
    adantr
    fveq2d
    wph
    @73
    cD
    wceq
    #
    @64
    @71
    wph
    @69
    @70
    @74
    curfval.c
    curfval.d
    cC
    cD
    ccat
    ccat
    op2ndg
    syl2anc
    ad2antrr
    eqtrd
    @72
    @33
    cD
    wceq
    #
    wa
    #
    @49
    @18
    @58
    @26
    @76
    vx
    @32
    @48
    cA
    @17
    @76
    @32
    cC
    cbs
    cfv
    cA
    @76
    @31
    cC
    cbs
    @65
    @71
    @75
    simplr
    #
    fveq2d
    curfval.a
    syl6eqr
    #
    @76
    @38
    @5
    @47
    @16
    @76
    vy
    @34
    @37
    cB
    @4
    @76
    @34
    cD
    cbs
    cfv
    cB
    @76
    @33
    cD
    cbs
    @72
    @75
    simpr
    #
    fveq2d
    curfval.b
    syl6eqr
    #
    @76
    @36
    @3
    @1
    @2
    @76
    @35
    cF
    c1st
    @65
    @63
    @71
    @75
    wph
    @62
    @63
    simprr
    ad2antrr
    #
    fveq2d
    oveqd
    mpteq12dv
    @76
    vy
    vz
    @34
    @34
    @46
    cB
    cB
    @15
    @80
    @80
    @76
    vg
    @40
    @45
    @7
    @14
    @76
    @39
    cJ
    @2
    @6
    @76
    @39
    cD
    chom
    cfv
    cJ
    @76
    @33
    cD
    chom
    @79
    fveq2d
    curfval.j
    syl6eqr
    oveqd
    @76
    @42
    @8
    @9
    @9
    @44
    @13
    @76
    @43
    @12
    @10
    @11
    @76
    @35
    cF
    c2nd
    @81
    fveq2d
    #
    oveqd
    @76
    @1
    @41
    c.1
    @76
    @41
    cC
    ccid
    cfv
    c.1
    @76
    @31
    cC
    ccid
    @77
    fveq2d
    curfval.1
    syl6eqr
    fveq1d
    @76
    @9
    eqidd
    #
    oveq123d
    mpteq12dv
    mpt2eq123dv
    opeq12d
    mpteq12dv
    @76
    vx
    vy
    @32
    @32
    @57
    cA
    cA
    @25
    @78
    @78
    @76
    vg
    @51
    @56
    @19
    @24
    @76
    @50
    cH
    @1
    @2
    @76
    @50
    cC
    chom
    cfv
    cH
    @76
    @31
    cC
    chom
    @77
    fveq2d
    curfval.h
    syl6eqr
    oveqd
    @76
    vz
    @34
    @55
    cB
    @23
    @80
    @76
    @9
    @9
    @53
    @20
    @54
    @22
    @76
    @43
    @12
    @11
    @21
    @82
    oveqd
    @83
    @76
    @6
    @52
    cI
    @76
    @52
    cD
    ccid
    cfv
    cI
    @76
    @33
    cD
    ccid
    @79
    fveq2d
    curfval.i
    syl6eqr
    fveq1d
    oveq123d
    mpteq12dv
    mpteq12dv
    mpt2eq123dv
    opeq12d
    csbied2
    csbied2
    @0
    cvv
    wcel
    wph
    cC
    cD
    opex
    a1i
    wph
    cF
    cC
    cD
    cxpc
    co
    cE
    cfunc
    co
    #
    wcel
    cF
    cvv
    wcel
    curfval.f
    cF
    @84
    elex
    syl
    @27
    cvv
    wcel
    wph
    @18
    @26
    opex
    a1i
    ovmpt2d
    syl5eq
end
