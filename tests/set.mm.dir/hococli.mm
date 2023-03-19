include "chil.mm"
include "wcel.mm"
include "ccom.mm"
include "cfv.mm"
include "hocoi.mm"
include "ffvelrni.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem hococli
  let cA: class A
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( A e. ~H -> ( ( S o. T ) ` A ) e. ~H )

  proof
    cA
    chil
    wcel
    #
    cA
    cS
    cT
    ccom
    cfv
    cA
    cT
    cfv
    #
    cS
    cfv
    #
    chil
    cA
    cS
    cT
    hoeq.1
    hoeq.2
    hocoi
    @0
    @1
    chil
    wcel
    @2
    chil
    wcel
    chil
    chil
    cA
    cT
    hoeq.2
    ffvelrni
    chil
    chil
    @1
    cS
    hoeq.1
    ffvelrni
    syl
    eqeltrd
end
