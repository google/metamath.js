include "wcel.mm"
include "wbr.mm"
include "wsbc.mm"
include "csb.mm"
include "sbcbr12g.mm"
include "csbconstg.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem sbcbr1g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V

  disjoint C x
  disjoint R x
  assert |- ( A e. V -> ( [. A / x ]. B R C <-> [_ A / x ]_ B R C ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cC
    cR
    wbr
    vx
    cA
    wsbc
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    cR
    wbr
    @1
    cC
    cR
    wbr
    vx
    cA
    cB
    cC
    cR
    cV
    sbcbr12g
    @0
    @2
    cC
    @1
    cR
    vx
    cA
    cC
    cV
    csbconstg
    breq2d
    bitrd
end
