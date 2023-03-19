include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "caov.mm"
include "cop.mm"
include "cafv.mm"
include "df-aov.mm"
include "cdm.mm"
include "wceq.mm"
include "wbr.mm"
include "df-br.mm"
include "wrel.mm"
include "brrelex12.mm"
include "mpan.mm"
include "sylbir.mm"
include "con3i.mm"
include "ndmafv.mm"
include "syl.mm"
include "syl5eq.mm"

theorem aovprc
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume aovprc.1: |- Rel dom F


  assert |- ( -. ( A e. _V /\ B e. _V ) -> (( A F B )) = _V )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    wn
    #
    cA
    cB
    cF
    caov
    cA
    cB
    cop
    #
    cF
    cafv
    #
    cvv
    cA
    cB
    cF
    df-aov
    @1
    @2
    cF
    cdm
    #
    wcel
    #
    wn
    @3
    cvv
    wceq
    @5
    @0
    @5
    cA
    cB
    @4
    wbr
    #
    @0
    cA
    cB
    @4
    df-br
    @4
    wrel
    @6
    @0
    aovprc.1
    cA
    cB
    @4
    brrelex12
    mpan
    sylbir
    con3i
    @2
    cF
    ndmafv
    syl
    syl5eq
end
