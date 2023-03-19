include "cres.mm"
include "cin.mm"
include "crn.mm"
include "cima.mm"
include "rnin.mm"
include "df-ima.mm"
include "resindir.mm"
include "rneqi.mm"
include "eqtri.mm"
include "ineq12i.mm"
include "3sstr4i.mm"

theorem inimass
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) " C ) C_ ( ( A " C ) i^i ( B " C ) )

  proof
    cA
    cC
    cres
    #
    cB
    cC
    cres
    #
    cin
    #
    crn
    #
    @0
    crn
    #
    @1
    crn
    #
    cin
    cA
    cB
    cin
    #
    cC
    cima
    #
    cA
    cC
    cima
    #
    cB
    cC
    cima
    #
    cin
    @0
    @1
    rnin
    @7
    @6
    cC
    cres
    #
    crn
    @3
    @6
    cC
    df-ima
    @10
    @2
    cA
    cB
    cC
    resindir
    rneqi
    eqtri
    @8
    @4
    @9
    @5
    cA
    cC
    df-ima
    cB
    cC
    df-ima
    ineq12i
    3sstr4i
end
