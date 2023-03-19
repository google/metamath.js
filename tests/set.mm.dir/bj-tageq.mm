include "wceq.mm"
include "bj-csngl.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "bj-ctag.mm"
include "bj-sngleq.mm"
include "uneq1d.mm"
include "df-bj-tag.mm"
include "3eqtr4g.mm"

theorem bj-tageq
  let cA: class A
  let cB: class B


  assert |- ( A = B -> tag A = tag B )

  proof
    cA
    cB
    wceq
    #
    cA
    bj-csngl
    #
    c0
    csn
    #
    cun
    cB
    bj-csngl
    #
    @2
    cun
    cA
    bj-ctag
    cB
    bj-ctag
    @0
    @1
    @3
    @2
    cA
    cB
    bj-sngleq
    uneq1d
    cA
    df-bj-tag
    cB
    df-bj-tag
    3eqtr4g
end
