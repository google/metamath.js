include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wss.mm"
include "elocv.mm"
include "simp3bi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem ocvi
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let c.xi: class .,
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vh: setvar h
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  assume ocvfval.v: |- V = ( Base ` W )
  assume ocvfval.i: |- ., = ( .i ` W )
  assume ocvfval.f: |- F = ( Scalar ` W )
  assume ocvfval.z: |- .0. = ( 0g ` F )
  assume ocvfval.o: |- ._|_ = ( ocv ` W )


  assert |- ( ( A e. ( ._|_ ` S ) /\ B e. S ) -> ( A ., B ) = .0. )

  proof
    cA
    cS
    c.pe
    cfv
    wcel
    #
    cA
    vx
    cv
    #
    c.xi
    co
    #
    c.0
    wceq
    #
    vx
    cS
    wral
    #
    cB
    cS
    wcel
    cA
    cB
    c.xi
    co
    #
    c.0
    wceq
    #
    @0
    cS
    cV
    wss
    cA
    cV
    wcel
    @4
    vx
    cA
    cS
    cF
    c.xi
    c.pe
    cV
    cW
    c.0
    ocvfval.v
    ocvfval.i
    ocvfval.f
    ocvfval.z
    ocvfval.o
    elocv
    simp3bi
    @3
    @6
    vx
    cB
    cS
    @1
    cB
    wceq
    @2
    @5
    c.0
    @1
    cB
    cA
    c.xi
    oveq2
    eqeq1d
    rspccva
    sylan
end
