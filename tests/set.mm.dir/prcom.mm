include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "uncom.mm"
include "df-pr.mm"
include "3eqtr4i.mm"

theorem prcom
  param cA: class A
  param cB: class B


  assert |- { A , B } = { B , A }

  proof
    cA
    csn
    #
    cB
    csn
    #
    cun
    @1
    @0
    cun
    cA
    cB
    cpr
    cB
    cA
    cpr
    @0
    @1
    uncom
    cA
    cB
    df-pr
    cB
    cA
    df-pr
    3eqtr4i
end
