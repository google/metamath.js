include "cun.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "resundi.mm"
include "rneqi.mm"
include "rnun.mm"
include "eqtri.mm"
include "df-ima.mm"
include "uneq12i.mm"
include "3eqtr4i.mm"

theorem imaundi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A " ( B u. C ) ) = ( ( A " B ) u. ( A " C ) )

  proof
    cA
    cB
    cC
    cun
    #
    cres
    #
    crn
    #
    cA
    cB
    cres
    #
    crn
    #
    cA
    cC
    cres
    #
    crn
    #
    cun
    #
    cA
    @0
    cima
    cA
    cB
    cima
    #
    cA
    cC
    cima
    #
    cun
    @2
    @3
    @5
    cun
    #
    crn
    @7
    @1
    @10
    cA
    cB
    cC
    resundi
    rneqi
    @3
    @5
    rnun
    eqtri
    cA
    @0
    df-ima
    @8
    @4
    @9
    @6
    cA
    cB
    df-ima
    cA
    cC
    df-ima
    uneq12i
    3eqtr4i
end
