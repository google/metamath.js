include "caov.mm"
include "wcel.mm"
include "cop.mm"
include "cdm.mm"
include "wa.mm"
include "aovvdm.mm"
include "cxp.mm"
include "opelxp.mm"
include "biimpi.mm"
include "eleq2s.mm"
include "syl.mm"

theorem ndmaovrcl
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume ndmaov.1: |- dom F = ( S X. S )


  assert |- ( (( A F B )) e. S -> ( A e. S /\ B e. S ) )

  proof
    cA
    cB
    cF
    caov
    cS
    wcel
    cA
    cB
    cop
    #
    cF
    cdm
    #
    wcel
    cA
    cS
    wcel
    cB
    cS
    wcel
    wa
    #
    cA
    cB
    cS
    cF
    aovvdm
    @2
    @0
    cS
    cS
    cxp
    #
    @1
    @0
    @3
    wcel
    @2
    cA
    cB
    cS
    cS
    opelxp
    biimpi
    ndmaov.1
    eleq2s
    syl
end
