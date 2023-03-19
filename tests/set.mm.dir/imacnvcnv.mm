include "ccnv.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "rescnvcnv.mm"
include "rneqi.mm"
include "df-ima.mm"
include "3eqtr4i.mm"

theorem imacnvcnv
  let cA: class A
  let cB: class B


  assert |- ( `' `' A " B ) = ( A " B )

  proof
    cA
    ccnv
    ccnv
    #
    cB
    cres
    #
    crn
    cA
    cB
    cres
    #
    crn
    @0
    cB
    cima
    cA
    cB
    cima
    @1
    @2
    cA
    cB
    rescnvcnv
    rneqi
    @0
    cB
    df-ima
    cA
    cB
    df-ima
    3eqtr4i
end
