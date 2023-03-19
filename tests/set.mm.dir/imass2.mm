include "wss.mm"
include "cres.mm"
include "crn.mm"
include "cima.mm"
include "ssres2.mm"
include "rnss.mm"
include "syl.mm"
include "df-ima.mm"
include "3sstr4g.mm"

theorem imass2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ B -> ( C " A ) C_ ( C " B ) )

  proof
    cA
    cB
    wss
    #
    cC
    cA
    cres
    #
    crn
    #
    cC
    cB
    cres
    #
    crn
    #
    cC
    cA
    cima
    cC
    cB
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
    ssres2
    @1
    @3
    rnss
    syl
    cC
    cA
    df-ima
    cC
    cB
    df-ima
    3sstr4g
end
