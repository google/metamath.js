include "wceq.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "ctp.mm"
include "preq1.mm"
include "uneq1d.mm"
include "df-tp.mm"
include "3eqtr4g.mm"

theorem tpeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A = B -> { A , C , D } = { B , C , D } )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    cpr
    #
    cD
    csn
    #
    cun
    cB
    cC
    cpr
    #
    @2
    cun
    cA
    cC
    cD
    ctp
    cB
    cC
    cD
    ctp
    @0
    @1
    @3
    @2
    cA
    cB
    cC
    preq1
    uneq1d
    cA
    cC
    cD
    df-tp
    cB
    cC
    cD
    df-tp
    3eqtr4g
end
