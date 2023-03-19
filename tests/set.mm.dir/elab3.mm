include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "cab.mm"
include "wb.mm"
include "elab3g.mm"
include "ax-mp.mm"

theorem elab3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume elab3.1: |- ( ps -> A e. _V )
  assume elab3.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  assert |- ( A e. { x | ph } <-> ps )

  proof
    wps
    cA
    cvv
    wcel
    wi
    cA
    wph
    vx
    cab
    wcel
    wps
    wb
    elab3.1
    wph
    wps
    vx
    cA
    cvv
    elab3.2
    elab3g
    ax-mp
end
