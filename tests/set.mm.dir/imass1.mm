include "wss.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "ssres.mm"
include "rnss.mm"
include "syl.mm"
include "df-ima.mm"
include "3sstr4g.mm"

theorem imass1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> ( A " C ) C_ ( B " C ) )

  proof
    cA
    cB
    wss
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
    cA
    cC
    cima
    cB
    cC
    cima
    @0
    @1
    @3
    wss
    @2
    @4
    wss
    cA
    cB
    cC
    ssres
    @1
    @3
    rnss
    syl
    cA
    cC
    df-ima
    cB
    cC
    df-ima
    3sstr4g
end
