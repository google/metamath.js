include "ccph.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "csqrt.mm"
include "cmpt.mm"
include "cphnmfval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "oveq12.mm"
include "anidms.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem cphnm
  let cA: class A
  let c.xi: class .,
  let cN: class N
  let cV: class V
  let cW: class W
  let vx: setvar x
  let cK: class K
  assume nmsq.v: |- V = ( Base ` W )
  assume nmsq.h: |- ., = ( .i ` W )
  assume nmsq.n: |- N = ( norm ` W )


  assert |- ( ( W e. CPreHil /\ A e. V ) -> ( N ` A ) = ( sqrt ` ( A ., A ) ) )

  proof
    cW
    ccph
    wcel
    #
    cA
    cV
    wcel
    cA
    cN
    cfv
    cA
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
    cA
    cA
    c.xi
    co
    #
    csqrt
    cfv
    #
    @0
    cA
    cN
    @4
    vx
    c.xi
    cN
    cV
    cW
    nmsq.v
    nmsq.h
    nmsq.n
    cphnmfval
    fveq1d
    vx
    cA
    @3
    @6
    cV
    @4
    @1
    cA
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
    cA
    @1
    cA
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
