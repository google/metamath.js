include "wceq.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "reseq1.mm"
include "rneqd.mm"
include "df-ima.mm"
include "3eqtr4g.mm"

theorem imaeq1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( A " C ) = ( B " C ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cC
    cres
    #
    crn
    cB
    cC
    cres
    #
    crn
    cA
    cC
    cima
    cB
    cC
    cima
    @0
    @1
    @2
    cA
    cB
    cC
    reseq1
    rneqd
    cA
    cC
    df-ima
    cB
    cC
    df-ima
    3eqtr4g
end
