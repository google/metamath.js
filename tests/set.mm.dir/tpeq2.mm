include "wceq.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "ctp.mm"
include "preq2.mm"
include "uneq1d.mm"
include "df-tp.mm"
include "3eqtr4g.mm"

theorem tpeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A = B -> { C , A , D } = { C , B , D } )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    cpr
    #
    cD
    csn
    #
    cun
    cC
    cB
    cpr
    #
    @2
    cun
    cC
    cA
    cD
    ctp
    cC
    cB
    cD
    ctp
    @0
    @1
    @3
    @2
    cA
    cB
    cC
    preq2
    uneq1d
    cC
    cA
    cD
    df-tp
    cC
    cB
    cD
    df-tp
    3eqtr4g
end
