include "ccph.mm"
include "wcel.mm"
include "cphnmf.mm"
include "ffvelrnda.mm"

theorem cphnmcl
  let cA: class A
  let cF: class F
  let c.xi: class .,
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume nmsq.v: |- V = ( Base ` W )
  assume nmsq.h: |- ., = ( .i ` W )
  assume nmsq.n: |- N = ( norm ` W )
  assume cphnmcl.f: |- F = ( Scalar ` W )
  assume cphnmcl.k: |- K = ( Base ` F )


  assert |- ( ( W e. CPreHil /\ A e. V ) -> ( N ` A ) e. K )

  proof
    cW
    ccph
    wcel
    cV
    cK
    cA
    cN
    cF
    c.xi
    cK
    cN
    cV
    cW
    nmsq.v
    nmsq.h
    nmsq.n
    cphnmcl.f
    cphnmcl.k
    cphnmf
    ffvelrnda
end
