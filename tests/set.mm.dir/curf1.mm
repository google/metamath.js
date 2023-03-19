include "c1st.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "cop.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "cvv.mm"
include "curf1fval.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "oveq1d.mm"
include "mpteq2dv.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1r.mm"
include "opeq1d.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpt2eq3dva.mm"
include "opeq12d.mm"
include "opex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem curf1
  let wph: wff ph
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
  let cJ: class J
  let cK: class K
  let cX: class X
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vx: setvar x
  let vh: setvar h
  let vw: setvar w
  let cH: class H
  let cI: class I
  let cY: class Y
  let cZ: class Z
  assume curfval.g: |- G = ( <. C , D >. curryF F )
  assume curfval.a: |- A = ( Base ` C )
  assume curfval.c: |- ( ph -> C e. Cat )
  assume curfval.d: |- ( ph -> D e. Cat )
  assume curfval.f: |- ( ph -> F e. ( ( C Xc. D ) Func E ) )
  assume curfval.b: |- B = ( Base ` D )
  assume curf1.x: |- ( ph -> X e. A )
  assume curf1.k: |- K = ( ( 1st ` G ) ` X )
  assume curf1.j: |- J = ( Hom ` D )
  assume curf1.1: |- .1. = ( Id ` C )

  disjoint g y
  disjoint g z
  disjoint .1. g
  disjoint y z
  disjoint .1. y
  disjoint .1. z
  disjoint A y
  disjoint B g
  disjoint B y
  disjoint B z
  disjoint C g
  disjoint C y
  disjoint C z
  disjoint D g
  disjoint D y
  disjoint D z
  disjoint g ph
  disjoint ph y
  disjoint ph z
  disjoint E g
  disjoint E y
  disjoint E z
  disjoint J g
  disjoint K g
  disjoint K y
  disjoint K z
  disjoint X g
  disjoint X y
  disjoint X z
  disjoint F g
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
  disjoint g x
  disjoint x y
  disjoint x z
  disjoint .1. x
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A f
  disjoint A x
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
  disjoint B x
  disjoint C c
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C x
  disjoint D c
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D h
  disjoint D w
  disjoint D x
  disjoint H c
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint H g
  disjoint H y
  disjoint H z
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
  disjoint ph x
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
  disjoint J x
  disjoint K h
  disjoint K w
  disjoint X x
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F x
  assert |- ( ph -> K = <. ( y e. B |-> ( X ( 1st ` F ) y ) ) , ( y e. B , z e. B |-> ( g e. ( y J z ) |-> ( ( .1. ` X ) ( <. X , y >. ( 2nd ` F ) <. X , z >. ) g ) ) ) >. )

  proof
    wph
    cK
    cX
    cG
    c1st
    cfv
    #
    cfv
    vy
    cB
    cX
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
    @1
    vz
    cv
    #
    cJ
    co
    #
    cX
    c.1
    cfv
    #
    vg
    cv
    #
    cX
    @1
    cop
    #
    cX
    @5
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
    curf1.k
    wph
    vx
    cX
    vy
    cB
    vx
    cv
    #
    @1
    @2
    co
    #
    cmpt
    #
    vy
    vz
    cB
    cB
    vg
    @6
    @17
    c.1
    cfv
    #
    @8
    @17
    @1
    cop
    #
    @17
    @5
    cop
    #
    @11
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cop
    @16
    cA
    @0
    cvv
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    cD
    c.1
    vg
    cE
    cF
    cG
    cJ
    curfval.g
    curfval.a
    curfval.c
    curfval.d
    curfval.f
    curfval.b
    curf1.j
    curf1.1
    curf1fval
    wph
    @17
    cX
    wceq
    #
    wa
    #
    @19
    @4
    @26
    @15
    @28
    vy
    cB
    @18
    @3
    @28
    @17
    cX
    @1
    @2
    wph
    @27
    simpr
    oveq1d
    mpteq2dv
    @28
    vy
    vz
    cB
    cB
    @25
    @14
    @28
    @1
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    w3a
    #
    vg
    @6
    @24
    @13
    @31
    @20
    @7
    @8
    @8
    @23
    @12
    @31
    @21
    @9
    @22
    @10
    @11
    @31
    @17
    cX
    @1
    wph
    @27
    @29
    @30
    simp1r
    #
    opeq1d
    @31
    @17
    cX
    @5
    @32
    opeq1d
    oveq12d
    @31
    @17
    cX
    c.1
    @32
    fveq2d
    @31
    @8
    eqidd
    oveq123d
    mpteq2dv
    mpt2eq3dva
    opeq12d
    curf1.x
    @16
    cvv
    wcel
    wph
    @4
    @15
    opex
    a1i
    fvmptd
    syl5eq
end
