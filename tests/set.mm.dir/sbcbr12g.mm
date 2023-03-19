include "wbr.mm"
include "wsbc.mm"
include "csb.mm"
include "wcel.mm"
include "sbcbr123.mm"
include "csbconstg.mm"
include "breqd.mm"
include "syl5bb.mm"

theorem sbcbr12g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cV: class V

  disjoint R x
  assert |- ( A e. V -> ( [. A / x ]. B R C <-> [_ A / x ]_ B R [_ A / x ]_ C ) )

  proof
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
    vx
    cA
    cR
    csb
    #
    wbr
    cA
    cV
    wcel
    #
    @0
    @1
    cR
    wbr
    vx
    cA
    cB
    cC
    cR
    sbcbr123
    @3
    @2
    cR
    @0
    @1
    vx
    cA
    cR
    cV
    csbconstg
    breqd
    syl5bb
end
