include "wceq.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "ineq1.mm"
include "df-res.mm"
include "3eqtr4g.mm"

theorem reseq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A |` C ) = ( B |` C ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    cvv
    cxp
    #
    cin
    cB
    @0
    cin
    cA
    cC
    cres
    cB
    cC
    cres
    cA
    cB
    @0
    ineq1
    cA
    cC
    df-res
    cB
    cC
    df-res
    3eqtr4g
end
