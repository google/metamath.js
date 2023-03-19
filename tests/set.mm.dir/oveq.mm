include "wceq.mm"
include "cop.mm"
include "cfv.mm"
include "co.mm"
include "fveq1.mm"
include "df-ov.mm"
include "3eqtr4g.mm"

theorem oveq
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G


  assert |- ( F = G -> ( A F B ) = ( A G B ) )

  proof
    cF
    cG
    wceq
    cA
    cB
    cop
    #
    cF
    cfv
    @0
    cG
    cfv
    cA
    cB
    cF
    co
    cA
    cB
    cG
    co
    @0
    cF
    cG
    fveq1
    cA
    cB
    cF
    df-ov
    cA
    cB
    cG
    df-ov
    3eqtr4g
end
