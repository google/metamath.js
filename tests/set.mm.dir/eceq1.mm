include "wceq.mm"
include "csn.mm"
include "cima.mm"
include "cec.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "df-ec.mm"
include "3eqtr4g.mm"

theorem eceq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> [ A ] C = [ B ] C )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    csn
    #
    cima
    cC
    cB
    csn
    #
    cima
    cA
    cC
    cec
    cB
    cC
    cec
    @0
    @1
    @2
    cC
    cA
    cB
    sneq
    imaeq2d
    cA
    cC
    df-ec
    cB
    cC
    df-ec
    3eqtr4g
end
