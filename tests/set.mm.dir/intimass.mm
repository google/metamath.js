include "cint.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cop.mm"
include "wcel.mm"
include "wral.mm"
include "r19.12.mm"
include "elimaint.mm"
include "elintima.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem intimass
  let vx: setvar x
  let cA: class A
  let cB: class B
  let va: setvar a
  let vy: setvar y
  let vb: setvar b

  disjoint a x
  disjoint A a
  disjoint A x
  disjoint B a
  disjoint B x
  disjoint a y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint A b
  disjoint B b
  disjoint a b
  disjoint b y
  disjoint b x
  assert |- ( |^| A " B ) C_ |^| { x | E. a e. A x = ( a " B ) }

  proof
    vy
    cA
    cint
    cB
    cima
    #
    vx
    cv
    va
    cv
    #
    cB
    cima
    wceq
    va
    cA
    wrex
    vx
    cab
    cint
    #
    vb
    cv
    vy
    cv
    #
    cop
    @1
    wcel
    #
    va
    cA
    wral
    vb
    cB
    wrex
    @4
    vb
    cB
    wrex
    va
    cA
    wral
    @3
    @0
    wcel
    @3
    @2
    wcel
    @4
    vb
    va
    cB
    cA
    r19.12
    vy
    cA
    cB
    va
    vb
    elimaint
    vx
    vy
    cA
    cB
    va
    vb
    elintima
    3imtr4i
    ssriv
end
