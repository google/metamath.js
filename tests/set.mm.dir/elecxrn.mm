include "cxrn.mm"
include "cec.mm"
include "wcel.mm"
include "wbr.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "w3a.mm"
include "wex.mm"
include "wrel.mm"
include "wb.mm"
include "xrnrel.mm"
include "relelec.mm"
include "ax-mp.mm"
include "brxrn2.mm"
include "syl5bb.mm"

theorem elecxrn
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cV: class V

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  disjoint V x
  disjoint V y
  assert |- ( A e. V -> ( B e. [ A ] ( R |X. S ) <-> E. x E. y ( B = <. x , y >. /\ A R x /\ A S y ) ) )

  proof
    cB
    cA
    cR
    cS
    cxrn
    #
    cec
    wcel
    #
    cA
    cB
    @0
    wbr
    #
    cA
    cV
    wcel
    cB
    vx
    cv
    #
    vy
    cv
    #
    cop
    wceq
    cA
    @3
    cR
    wbr
    cA
    @4
    cS
    wbr
    w3a
    vy
    wex
    vx
    wex
    @0
    wrel
    @1
    @2
    wb
    cR
    cS
    xrnrel
    cB
    cA
    @0
    relelec
    ax-mp
    vx
    vy
    cA
    cB
    cR
    cS
    cV
    brxrn2
    syl5bb
end
