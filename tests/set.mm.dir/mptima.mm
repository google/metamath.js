include "cmpt.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "cin.mm"
include "df-ima.mm"
include "resmpt3.mm"
include "rneqi.mm"
include "eqtri.mm"

theorem mptima
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint C x
  assert |- ( ( x e. A |-> B ) " C ) = ran ( x e. ( A i^i C ) |-> B )

  proof
    vx
    cA
    cB
    cmpt
    #
    cC
    cima
    @0
    cC
    cres
    #
    crn
    vx
    cA
    cC
    cin
    cB
    cmpt
    #
    crn
    @0
    cC
    df-ima
    @1
    @2
    vx
    cA
    cC
    cB
    resmpt3
    rneqi
    eqtri
end
