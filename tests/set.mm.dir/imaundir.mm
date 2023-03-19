include "cun.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "resundir.mm"
include "rneqi.mm"
include "rnun.mm"
include "3eqtri.mm"
include "uneq12i.mm"
include "eqtr4i.mm"

theorem imaundir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A u. B ) " C ) = ( ( A " C ) u. ( B " C ) )

  proof
    cA
    cB
    cun
    #
    cC
    cima
    #
    cA
    cC
    cres
    #
    crn
    #
    cB
    cC
    cres
    #
    crn
    #
    cun
    #
    cA
    cC
    cima
    #
    cB
    cC
    cima
    #
    cun
    @1
    @0
    cC
    cres
    #
    crn
    @2
    @4
    cun
    #
    crn
    @6
    @0
    cC
    df-ima
    @9
    @10
    cA
    cB
    cC
    resundir
    rneqi
    @2
    @4
    rnun
    3eqtri
    @7
    @3
    @8
    @5
    cA
    cC
    df-ima
    cB
    cC
    df-ima
    uneq12i
    eqtr4i
end
