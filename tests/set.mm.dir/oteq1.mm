include "wceq.mm"
include "cop.mm"
include "cotp.mm"
include "opeq1.mm"
include "opeq1d.mm"
include "df-ot.mm"
include "3eqtr4g.mm"

theorem oteq1
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A = B -> <. A , C , D >. = <. B , C , D >. )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    cop
    #
    cD
    cop
    cB
    cC
    cop
    #
    cD
    cop
    cA
    cC
    cD
    cotp
    cB
    cC
    cD
    cotp
    @0
    @1
    @2
    cD
    cA
    cB
    cC
    opeq1
    opeq1d
    cA
    cC
    cD
    df-ot
    cB
    cC
    cD
    df-ot
    3eqtr4g
end
