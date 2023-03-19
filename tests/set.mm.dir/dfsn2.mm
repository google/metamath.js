include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "df-pr.mm"
include "unidm.mm"
include "eqtr2i.mm"

theorem dfsn2
  let cA: class A


  assert |- { A } = { A , A }

  proof
    cA
    cA
    cpr
    cA
    csn
    #
    @0
    cun
    @0
    cA
    cA
    df-pr
    @0
    unidm
    eqtr2i
end
