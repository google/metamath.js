include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "tchnmfval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "oveq12.mm"
include "anidms.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem tchnmval
  let cG: class G
  let c.xi: class .,
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.mi: class .-
  let vx: setvar x
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cC: class C
  let wph: wff ph
  let c.x: class .x.
  let cY: class Y
  assume tchval.n: |- G = ( toCHil ` W )
  assume tchnmval.n: |- N = ( norm ` G )
  assume tchnmval.v: |- V = ( Base ` W )
  assume tchnmval.h: |- ., = ( .i ` W )


  assert |- ( ( W e. Grp /\ X e. V ) -> ( N ` X ) = ( sqrt ` ( X ., X ) ) )

  proof
    cW
    cgrp
    wcel
    #
    cX
    cV
    wcel
    cX
    cN
    cfv
    cX
    vx
    cV
    vx
    cv
    #
    @1
    c.xi
    co
    #
    csqrt
    cfv
    #
    cmpt
    #
    cfv
    cX
    cX
    c.xi
    co
    #
    csqrt
    cfv
    #
    @0
    cX
    cN
    @4
    vx
    cG
    c.xi
    cN
    cV
    cW
    tchval.n
    tchnmval.n
    tchnmval.v
    tchnmval.h
    tchnmfval
    fveq1d
    vx
    cX
    @3
    @6
    cV
    @4
    @1
    cX
    wceq
    #
    @2
    @5
    csqrt
    @7
    @2
    @5
    wceq
    @1
    cX
    @1
    cX
    c.xi
    oveq12
    anidms
    fveq2d
    @4
    eqid
    @5
    csqrt
    fvex
    fvmpt
    sylan9eq
end
