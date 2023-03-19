include "nfv.mm"
include "vtoclf.mm"

theorem vtoclALT
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume vtocl.1: |- A e. _V
  assume vtocl.2: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl.3: |- ph

  disjoint A x
  disjoint ps x
  assert |- ps

  proof
    wph
    wps
    vx
    cA
    wps
    vx
    nfv
    vtocl.1
    vtocl.2
    vtocl.3
    vtoclf
end
