include "wceq.mm"
include "cop.mm"
include "cotp.mm"
include "opeq2.mm"
include "df-ot.mm"
include "3eqtr4g.mm"

theorem oteq3
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A = B -> <. C , D , A >. = <. C , D , B >. )

  proof
    cA
    cB
    wceq
    cC
    cD
    cop
    #
    cA
    cop
    @0
    cB
    cop
    cC
    cD
    cA
    cotp
    cC
    cD
    cB
    cotp
    cA
    cB
    @0
    opeq2
    cC
    cD
    cA
    df-ot
    cC
    cD
    cB
    df-ot
    3eqtr4g
end
