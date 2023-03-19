include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "ctp.mm"
include "dfsn2.mm"
include "uneq1i.mm"
include "df-pr.mm"
include "df-tp.mm"
include "3eqtr4ri.mm"

theorem tpidm12
  let cA: class A
  let cB: class B


  assert |- { A , A , B } = { A , B }

  proof
    cA
    csn
    #
    cB
    csn
    #
    cun
    cA
    cA
    cpr
    #
    @1
    cun
    cA
    cB
    cpr
    cA
    cA
    cB
    ctp
    @0
    @2
    @1
    cA
    dfsn2
    uneq1i
    cA
    cB
    df-pr
    cA
    cA
    cB
    df-tp
    3eqtr4ri
end
