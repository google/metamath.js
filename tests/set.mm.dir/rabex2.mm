include "cvv.mm"
include "wcel.mm"
include "id.mm"
include "rabexd.mm"
include "ax-mp.mm"

theorem rabex2
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume rabex2.1: |- B = { x e. A | ps }
  assume rabex2.2: |- A e. _V

  disjoint A x
  assert |- B e. _V

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    rabex2.2
    @0
    wps
    vx
    cA
    cB
    cvv
    rabex2.1
    @0
    id
    rabexd
    ax-mp
end
