include "wceq.mm"
include "cop.mm"
include "cfv.mm"
include "co.mm"
include "opeq1.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "3eqtr4g.mm"

theorem oveq1
  param cA: class A
  param cB: class B
  param cC: class C
  param cF: class F


  assert |- ( A = B -> ( A F C ) = ( B F C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    cop
    #
    cF
    cfv
    cB
    cC
    cop
    #
    cF
    cfv
    cA
    cC
    cF
    co
    cB
    cC
    cF
    co
    @0
    @1
    @2
    cF
    cA
    cB
    cC
    opeq1
    fveq2d
    cA
    cC
    cF
    df-ov
    cB
    cC
    cF
    df-ov
    3eqtr4g
end
