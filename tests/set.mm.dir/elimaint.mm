include "cv.mm"
include "cint.mm"
include "cima.mm"
include "wcel.mm"
include "wbr.mm"
include "wrex.mm"
include "cop.mm"
include "wral.mm"
include "vex.mm"
include "elima.mm"
include "df-br.mm"
include "opex.mm"
include "elint2.mm"
include "bitri.mm"
include "rexbii.mm"

theorem elimaint
  let vy: setvar y
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b

  disjoint a b
  disjoint A a
  disjoint A b
  disjoint B b
  disjoint a y
  disjoint b y
  assert |- ( y e. ( |^| A " B ) <-> E. b e. B A. a e. A <. b , y >. e. a )

  proof
    vy
    cv
    #
    cA
    cint
    #
    cB
    cima
    wcel
    vb
    cv
    #
    @0
    @1
    wbr
    #
    vb
    cB
    wrex
    @2
    @0
    cop
    #
    va
    cv
    wcel
    va
    cA
    wral
    #
    vb
    cB
    wrex
    vb
    @0
    @1
    cB
    vy
    vex
    elima
    @3
    @5
    vb
    cB
    @3
    @4
    @1
    wcel
    @5
    @2
    @0
    @1
    df-br
    va
    @4
    cA
    @2
    @0
    opex
    elint2
    bitri
    rexbii
    bitri
end
