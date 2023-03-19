include "cres.mm"
include "crn.mm"
include "cima.mm"
include "residm.mm"
include "rneqi.mm"
include "df-ima.mm"
include "3eqtr4i.mm"

theorem resima
  let cA: class A
  let cB: class B


  assert |- ( ( A |` B ) " B ) = ( A " B )

  proof
    cA
    cB
    cres
    #
    cB
    cres
    #
    crn
    @0
    crn
    @0
    cB
    cima
    cA
    cB
    cima
    @1
    @0
    cA
    cB
    residm
    rneqi
    @0
    cB
    df-ima
    cA
    cB
    df-ima
    3eqtr4i
end
