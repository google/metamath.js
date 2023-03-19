include "cv.mm"
include "cfv.mm"
include "cop.mm"
include "cmpt2.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "wceq.mm"
include "vex.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op2ndd.mm"
include "opeq12d.mm"
include "mpt2mpt.mm"
include "eqtr4i.mm"

theorem ucnimalem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cU: class U
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume ucnprima.1: |- ( ph -> U e. ( UnifOn ` X ) )
  assume ucnprima.2: |- ( ph -> V e. ( UnifOn ` Y ) )
  assume ucnprima.3: |- ( ph -> F e. ( U uCn V ) )
  assume ucnprima.4: |- ( ph -> W e. V )
  assume ucnprima.5: |- G = ( x e. X , y e. X |-> <. ( F ` x ) , ( F ` y ) >. )

  disjoint p x
  disjoint p y
  disjoint F p
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X p
  disjoint X x
  disjoint X y
  assert |- G = ( p e. ( X X. X ) |-> <. ( F ` ( 1st ` p ) ) , ( F ` ( 2nd ` p ) ) >. )

  proof
    cG
    vx
    vy
    cX
    cX
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cop
    #
    cmpt2
    vp
    cX
    cX
    cxp
    vp
    cv
    #
    c1st
    cfv
    #
    cF
    cfv
    #
    @5
    c2nd
    cfv
    #
    cF
    cfv
    #
    cop
    #
    cmpt
    ucnprima.5
    vx
    vy
    vp
    cX
    cX
    @10
    @4
    @5
    @0
    @2
    cop
    wceq
    #
    @7
    @1
    @9
    @3
    @11
    @6
    @0
    cF
    @0
    @2
    @5
    vx
    vex
    #
    vy
    vex
    #
    op1std
    fveq2d
    @11
    @8
    @2
    cF
    @0
    @2
    @5
    @12
    @13
    op2ndd
    fveq2d
    opeq12d
    mpt2mpt
    eqtr4i
end
