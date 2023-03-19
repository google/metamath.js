include "cres.mm"
include "cdm.mm"
include "crn.mm"
include "cima.mm"
include "resdmres.mm"
include "rneqi.mm"
include "df-ima.mm"
include "3eqtr4i.mm"

theorem imadmres
  let cA: class A
  let cB: class B


  assert |- ( A " dom ( A |` B ) ) = ( A " B )

  proof
    cA
    cA
    cB
    cres
    #
    cdm
    #
    cres
    #
    crn
    @0
    crn
    cA
    @1
    cima
    cA
    cB
    cima
    @2
    @0
    cA
    cB
    resdmres
    rneqi
    cA
    @1
    df-ima
    cA
    cB
    df-ima
    3eqtr4i
end
