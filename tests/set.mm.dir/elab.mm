include "nfv.mm"
include "elabf.mm"

theorem elab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume elab.1: |- A e. _V
  assume elab.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint ps x
  disjoint A x
  assert |- ( A e. { x | ph } <-> ps )

  proof
    wph
    wps
    vx
    cA
    wps
    vx
    nfv
    elab.1
    elab.2
    elabf
end
