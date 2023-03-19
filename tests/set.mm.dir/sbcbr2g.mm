include "wcel.mm"
include "wbr.mm"
include "wsbc.mm"
include "csb.mm"
include "sbcbr12g.mm"
include "csbconstg.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem sbcbr2g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V

  disjoint B x
  disjoint R x
  assert |- ( A e. V -> ( [. A / x ]. B R C <-> B R [_ A / x ]_ C ) )

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
    cB
    @2
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
    @1
    cB
    @2
    cR
    vx
    cA
    cB
    cV
    csbconstg
    breq1d
    bitrd
end
