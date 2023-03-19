include "cvv.mm"
include "wcel.mm"
include "wb.mm"
include "elab2g.mm"
include "ax-mp.mm"

theorem elab2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elab2.1: |- A e. _V
  assume elab2.2: |- ( x = A -> ( ph <-> ps ) )
  assume elab2.3: |- B = { x | ph }

  disjoint ps x
  disjoint A x
  assert |- ( A e. B <-> ps )

  proof
    cA
    cvv
    wcel
    cA
    cB
    wcel
    wps
    wb
    elab2.1
    wph
    wps
    vx
    cA
    cB
    cvv
    elab2.2
    elab2.3
    elab2g
    ax-mp
end
