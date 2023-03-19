include "wceq.mm"
include "cop.mm"
include "cotp.mm"
include "opeq2.mm"
include "opeq1d.mm"
include "df-ot.mm"
include "3eqtr4g.mm"

theorem oteq2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A = B -> <. C , A , D >. = <. C , B , D >. )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    cop
    #
    cD
    cop
    cC
    cB
    cop
    #
    cD
    cop
    cC
    cA
    cD
    cotp
    cC
    cB
    cD
    cotp
    @0
    @1
    @2
    cD
    cA
    cB
    cC
    opeq2
    opeq1d
    cC
    cA
    cD
    df-ot
    cC
    cB
    cD
    df-ot
    3eqtr4g
end
