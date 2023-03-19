include "chil.mm"
include "wf.mm"
include "wcel.mm"
include "ccom.mm"
include "cfv.mm"
include "wceq.mm"
include "fvco3.mm"
include "mpan.mm"

theorem hocoi
  let cA: class A
  let cS: class S
  let cT: class T
  let vx: setvar x
  assume hoeq.1: |- S : ~H --> ~H
  assume hoeq.2: |- T : ~H --> ~H


  assert |- ( A e. ~H -> ( ( S o. T ) ` A ) = ( S ` ( T ` A ) ) )

  proof
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
    ccom
    cfv
    cA
    cT
    cfv
    cS
    cfv
    wceq
    hoeq.2
    chil
    chil
    cA
    cS
    cT
    fvco3
    mpan
end
