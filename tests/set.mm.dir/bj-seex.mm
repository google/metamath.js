include "wse.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "df-se.mm"
include "wceq.mm"
include "nfeq2.mm"
include "breq2.mm"
include "bj-rabbid.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylanb.mm"

theorem bj-seex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cR: class R
  let vy: setvar y
  assume bj-seex.nf: |- F/_ x B

  disjoint A x
  disjoint R x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint R y
  assert |- ( ( R Se A /\ B e. A ) -> { x e. A | x R B } e. _V )

  proof
    cA
    cR
    wse
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    cA
    crab
    #
    cvv
    wcel
    #
    vy
    cA
    wral
    cB
    cA
    wcel
    @0
    cB
    cR
    wbr
    #
    vx
    cA
    crab
    #
    cvv
    wcel
    #
    vy
    vx
    cA
    cR
    df-se
    @4
    @7
    vy
    cB
    cA
    @1
    cB
    wceq
    #
    @3
    @6
    cvv
    @8
    @2
    @5
    vx
    cA
    vx
    @1
    cB
    bj-seex.nf
    nfeq2
    @1
    cB
    @0
    cR
    breq2
    bj-rabbid
    eleq1d
    rspccva
    sylanb
end
