include "wceq.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "xpeq1.mm"
include "ineq2d.mm"
include "df-res.mm"
include "3eqtr4g.mm"

theorem reseq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C |` A ) = ( C |` B ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    cvv
    cxp
    #
    cin
    cC
    cB
    cvv
    cxp
    #
    cin
    cC
    cA
    cres
    cC
    cB
    cres
    @0
    @1
    @2
    cC
    cA
    cB
    cvv
    xpeq1
    ineq2d
    cC
    cA
    df-res
    cC
    cB
    df-res
    3eqtr4g
end
