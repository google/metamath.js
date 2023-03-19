include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "elab2g.mm"
include "biadan2.mm"

theorem elab4g
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume elab4g.1: |- ( x = A -> ( ph <-> ps ) )
  assume elab4g.2: |- B = { x | ph }

  disjoint ps x
  disjoint A x
  assert |- ( A e. B <-> ( A e. _V /\ ps ) )

  proof
    cA
    cB
    wcel
    cA
    cvv
    wcel
    wps
    cA
    cB
    elex
    wph
    wps
    vx
    cA
    cB
    cvv
    elab4g.1
    elab4g.2
    elab2g
    biadan2
end
