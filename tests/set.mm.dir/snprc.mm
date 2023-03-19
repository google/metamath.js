include "csn.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wex.mm"
include "wn.mm"
include "velsn.mm"
include "exbii.mm"
include "neq0.mm"
include "isset.mm"
include "3bitr4i.mm"
include "con1bii.mm"

theorem snprc
  let cA: class A
  let vx: setvar x


  assert |- ( -. A e. _V <-> { A } = (/) )

  proof
    cA
    csn
    #
    c0
    wceq
    #
    cA
    cvv
    wcel
    #
    vx
    cv
    #
    @0
    wcel
    #
    vx
    wex
    @3
    cA
    wceq
    #
    vx
    wex
    @1
    wn
    @2
    @4
    @5
    vx
    vx
    cA
    velsn
    exbii
    vx
    @0
    neq0
    vx
    cA
    isset
    3bitr4i
    con1bii
end
