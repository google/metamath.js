include "chil.mm"
include "wf.mm"
include "wcel.mm"
include "chos.mm"
include "co.mm"
include "cfv.mm"
include "hoscl.mm"
include "mpanl12.mm"

theorem hoscli
  let cA: class A
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( A e. ~H -> ( ( S +op T ) ` A ) e. ~H )

  proof
    chil
    chil
    cS
    wf
    chil
    chil
    cT
    wf
    cA
    chil
    wcel
    cA
    cS
    cT
    chos
    co
    cfv
    chil
    wcel
    hoeq.1
    hoeq.2
    cA
    cS
    cT
    hoscl
    mpanl12
end
