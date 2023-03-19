include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "oveq1.mm"
include "adantl.mm"
include "simpr.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem scmatrhmval
  let vx: setvar x
  let cA: class A
  let cR: class R
  let c.1: class .1.
  let cF: class F
  let c.as: class .*
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  assume scmatrhmval.k: |- K = ( Base ` R )
  assume scmatrhmval.a: |- A = ( N Mat R )
  assume scmatrhmval.o: |- .1. = ( 1r ` A )
  assume scmatrhmval.t: |- .* = ( .s ` A )
  assume scmatrhmval.f: |- F = ( x e. K |-> ( x .* .1. ) )

  disjoint K x
  disjoint R x
  disjoint V x
  disjoint X x
  disjoint .1. x
  disjoint .* x
  assert |- ( ( R e. V /\ X e. K ) -> ( F ` X ) = ( X .* .1. ) )

  proof
    cR
    cV
    wcel
    #
    cX
    cK
    wcel
    #
    wa
    #
    vx
    cX
    vx
    cv
    #
    c.1
    c.as
    co
    #
    cX
    c.1
    c.as
    co
    #
    cK
    cF
    cvv
    cF
    vx
    cK
    @4
    cmpt
    wceq
    @2
    scmatrhmval.f
    a1i
    @3
    cX
    wceq
    @4
    @5
    wceq
    @2
    @3
    cX
    c.1
    c.as
    oveq1
    adantl
    @0
    @1
    simpr
    @2
    cX
    c.1
    c.as
    ovexd
    fvmptd
end
