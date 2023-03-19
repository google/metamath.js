include "caov.mm"
include "wcel.mm"
include "cop.mm"
include "cafv.mm"
include "cvv.mm"
include "wa.mm"
include "df-aov.mm"
include "eleq1i.mm"
include "cdm.mm"
include "afvvdm.mm"
include "wbr.mm"
include "df-br.mm"
include "wrel.mm"
include "brrelex12.mm"
include "mpan.mm"
include "sylbir.mm"
include "syl.mm"
include "sylbi.mm"

theorem aovrcl
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume aovprc.1: |- Rel dom F


  assert |- ( (( A F B )) e. C -> ( A e. _V /\ B e. _V ) )

  proof
    cA
    cB
    cF
    caov
    #
    cC
    wcel
    cA
    cB
    cop
    #
    cF
    cafv
    #
    cC
    wcel
    #
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    @0
    @2
    cC
    cA
    cB
    cF
    df-aov
    eleq1i
    @3
    @1
    cF
    cdm
    #
    wcel
    #
    @4
    @1
    cC
    cF
    afvvdm
    @6
    cA
    cB
    @5
    wbr
    #
    @4
    cA
    cB
    @5
    df-br
    @5
    wrel
    @7
    @4
    aovprc.1
    cA
    cB
    @5
    brrelex12
    mpan
    sylbir
    syl
    sylbi
end
