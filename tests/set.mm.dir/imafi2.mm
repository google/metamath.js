include "cfn.mm"
include "wcel.mm"
include "cima.mm"
include "cres.mm"
include "crn.mm"
include "df-ima.mm"
include "wss.mm"
include "resss.mm"
include "ssfi.mm"
include "mpan2.mm"
include "rnfi.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem imafi2
  let cA: class A
  let cB: class B


  assert |- ( A e. Fin -> ( A " B ) e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cA
    cB
    cima
    cA
    cB
    cres
    #
    crn
    #
    cfn
    cA
    cB
    df-ima
    @0
    @1
    cfn
    wcel
    #
    @2
    cfn
    wcel
    @0
    @1
    cA
    wss
    @3
    cA
    cB
    resss
    cA
    @1
    ssfi
    mpan2
    @1
    rnfi
    syl
    syl5eqel
end
