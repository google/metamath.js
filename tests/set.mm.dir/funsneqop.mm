include "wceq.mm"
include "csn.mm"
include "cop.mm"
include "cvv.mm"
include "cxp.mm"
include "funsneqopsn.mm"
include "snex.mm"
include "opelvv.mm"
include "syl6eqel.mm"

theorem funsneqop
  let cA: class A
  let cB: class B
  let cG: class G
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume funsndifnop.a: |- A e. _V
  assume funsndifnop.b: |- B e. _V
  assume funsndifnop.g: |- G = { <. A , B >. }


  assert |- ( A = B -> G e. ( _V X. _V ) )

  proof
    cA
    cB
    wceq
    cG
    cA
    csn
    #
    @0
    cop
    cvv
    cvv
    cxp
    cA
    cB
    cG
    funsndifnop.a
    funsndifnop.b
    funsndifnop.g
    funsneqopsn
    @0
    @0
    cA
    snex
    #
    @1
    opelvv
    syl6eqel
end
