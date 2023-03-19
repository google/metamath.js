include "ccom.mm"
include "crn.mm"
include "cres.mm"
include "cima.mm"
include "rnco.mm"
include "df-ima.mm"
include "eqtr4i.mm"

theorem rnco2
  let cA: class A
  let cB: class B


  assert |- ran ( A o. B ) = ( A " ran B )

  proof
    cA
    cB
    ccom
    crn
    cA
    cB
    crn
    #
    cres
    crn
    cA
    @0
    cima
    cA
    cB
    rnco
    cA
    @0
    df-ima
    eqtr4i
end
