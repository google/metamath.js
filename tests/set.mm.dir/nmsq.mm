include "ccph.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "csqrt.mm"
include "cphnm.mm"
include "oveq1d.mm"
include "cc.mm"
include "cphipcl.mm"
include "3anidm23.mm"
include "sqsqrtd.mm"
include "eqtrd.mm"

theorem nmsq
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


  assert |- ( ( W e. CPreHil /\ A e. V ) -> ( ( N ` A ) ^ 2 ) = ( A ., A ) )

  proof
    cW
    ccph
    wcel
    #
    cA
    cV
    wcel
    #
    wa
    #
    cA
    cN
    cfv
    #
    c2
    cexp
    co
    cA
    cA
    c.xi
    co
    #
    csqrt
    cfv
    #
    c2
    cexp
    co
    @4
    @2
    @3
    @5
    c2
    cexp
    cA
    c.xi
    cN
    cV
    cW
    nmsq.v
    nmsq.h
    nmsq.n
    cphnm
    oveq1d
    @2
    @4
    @0
    @1
    @4
    cc
    wcel
    cA
    cA
    c.xi
    cV
    cW
    nmsq.v
    nmsq.h
    cphipcl
    3anidm23
    sqsqrtd
    eqtrd
end
