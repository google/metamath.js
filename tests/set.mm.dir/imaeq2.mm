include "wceq.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "reseq2.mm"
include "rneqd.mm"
include "df-ima.mm"
include "3eqtr4g.mm"

theorem imaeq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C " A ) = ( C " B ) )

  proof
    cA
    cB
    wceq
    #
    cC
    cA
    cres
    #
    crn
    cC
    cB
    cres
    #
    crn
    cC
    cA
    cima
    cC
    cB
    cima
    @0
    @1
    @2
    cA
    cB
    cC
    reseq2
    rneqd
    cC
    cA
    df-ima
    cC
    cB
    df-ima
    3eqtr4g
end
