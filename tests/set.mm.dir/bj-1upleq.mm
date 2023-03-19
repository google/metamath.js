include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "bj-c1upl.mm"
include "bj-xtageq.mm"
include "df-bj-1upl.mm"
include "3eqtr4g.mm"

theorem bj-1upleq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> (| A |) = (| B |) )

  proof
    cA
    cB
    wceq
    c0
    csn
    #
    cA
    bj-ctag
    cxp
    @0
    cB
    bj-ctag
    cxp
    cA
    bj-c1upl
    cB
    bj-c1upl
    cA
    cB
    @0
    bj-xtageq
    cA
    df-bj-1upl
    cB
    df-bj-1upl
    3eqtr4g
end
