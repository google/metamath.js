include "crab.mm"
include "csn.mm"
include "wceq.mm"
include "wcel.mm"
include "snid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "elrabi.mm"
include "syl.mm"

theorem rabsnel
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabsnel.1: |- B e. _V

  disjoint A x
  disjoint B x
  assert |- ( { x e. A | ph } = { B } -> B e. A )

  proof
    wph
    vx
    cA
    crab
    #
    cB
    csn
    #
    wceq
    #
    cB
    @0
    wcel
    #
    cB
    cA
    wcel
    @2
    @3
    cB
    @1
    wcel
    cB
    rabsnel.1
    snid
    @0
    @1
    cB
    eleq2
    mpbiri
    wph
    vx
    cB
    cA
    elrabi
    syl
end
