include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cop.mm"
include "c2nd.mm"
include "cmpt2.mm"
include "chom.mm"
include "ccid.mm"
include "wceq.mm"
include "eqid.mm"
include "curfval.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "mpt2ex.mm"
include "op1std.mm"
include "syl.mm"

theorem curf1fval
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
  let cJ: class J
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vh: setvar h
  let vw: setvar w
  let cH: class H
  let cI: class I
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
  assert |- ( ph -> ( 1st ` G ) = ( x e. A |-> <. ( y e. B |-> ( x ( 1st ` F ) y ) ) , ( y e. B , z e. B |-> ( g e. ( y J z ) |-> ( ( .1. ` x ) ( <. x , y >. ( 2nd ` F ) <. x , z >. ) g ) ) ) >. ) )

  proof
    wph
    cG
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
    co
    cmpt
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
    @0
    c.1
    cfv
    vg
    cv
    #
    @0
    @1
    cop
    @0
    @2
    cop
    #
    cF
    c2nd
    cfv
    #
    co
    co
    cmpt
    cmpt2
    cop
    #
    cmpt
    #
    vx
    vy
    cA
    cA
    vg
    @0
    @1
    cC
    chom
    cfv
    #
    co
    vz
    cB
    @3
    @2
    cD
    ccid
    cfv
    #
    cfv
    @4
    @1
    @2
    cop
    @5
    co
    co
    cmpt
    cmpt
    #
    cmpt2
    #
    cop
    wceq
    cG
    c1st
    cfv
    @7
    wceq
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
    @8
    @9
    cJ
    curfval.g
    curfval.a
    curfval.c
    curfval.d
    curfval.f
    curfval.b
    curfval.j
    curfval.1
    @8
    eqid
    @9
    eqid
    curfval
    @7
    @11
    cG
    vx
    cA
    @6
    cA
    cC
    cbs
    cfv
    cvv
    curfval.a
    cC
    cbs
    fvex
    eqeltri
    #
    mptex
    vx
    vy
    cA
    cA
    @10
    @12
    @12
    mpt2ex
    op1std
    syl
end
