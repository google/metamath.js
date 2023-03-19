include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "ctp.mm"
include "prcom.mm"
include "uneq1i.mm"
include "df-tp.mm"
include "3eqtr4i.mm"

theorem tpcoma
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- { A , B , C } = { B , A , C }

  proof
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
    cB
    cA
    cpr
    #
    @1
    cun
    cA
    cB
    cC
    ctp
    cB
    cA
    cC
    ctp
    @0
    @2
    @1
    cA
    cB
    prcom
    uneq1i
    cA
    cB
    cC
    df-tp
    cB
    cA
    cC
    df-tp
    3eqtr4i
end
