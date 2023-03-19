include "ctp.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "df-tp.mm"
include "prex.mm"
include "snex.mm"
include "unex.mm"
include "eqeltri.mm"

theorem tpex
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- { A , B , C } e. _V

  proof
    cA
    cB
    cC
    ctp
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
    cvv
    cA
    cB
    cC
    df-tp
    @0
    @1
    cA
    cB
    prex
    cC
    snex
    unex
    eqeltri
end
