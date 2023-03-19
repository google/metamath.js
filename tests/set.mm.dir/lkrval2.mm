include "wcel.mm"
include "cvv.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "crab.mm"
include "elex.mm"
include "wa.mm"
include "cab.mm"
include "ellkr.mm"
include "abbi2dv.mm"
include "df-rab.mm"
include "syl6eqr.mm"
include "sylan.mm"

theorem lkrval2
  let vx: setvar x
  let cD: class D
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume lkrfval2.v: |- V = ( Base ` W )
  assume lkrfval2.d: |- D = ( Scalar ` W )
  assume lkrfval2.o: |- .0. = ( 0g ` D )
  assume lkrfval2.f: |- F = ( LFnl ` W )
  assume lkrfval2.k: |- K = ( LKer ` W )

  disjoint F x
  disjoint G x
  disjoint K x
  disjoint W x
  assert |- ( ( W e. X /\ G e. F ) -> ( K ` G ) = { x e. V | ( G ` x ) = .0. } )

  proof
    cW
    cX
    wcel
    cW
    cvv
    wcel
    #
    cG
    cF
    wcel
    #
    cG
    cK
    cfv
    #
    vx
    cv
    #
    cG
    cfv
    c.0
    wceq
    #
    vx
    cV
    crab
    #
    wceq
    cW
    cX
    elex
    @0
    @1
    wa
    #
    @2
    @3
    cV
    wcel
    @4
    wa
    #
    vx
    cab
    @5
    @6
    @7
    vx
    @2
    cD
    cF
    cG
    cK
    cV
    cW
    @3
    cvv
    c.0
    lkrfval2.v
    lkrfval2.d
    lkrfval2.o
    lkrfval2.f
    lkrfval2.k
    ellkr
    abbi2dv
    @4
    vx
    cV
    df-rab
    syl6eqr
    sylan
end
