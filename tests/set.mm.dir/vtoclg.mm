include "nfv.mm"
include "vtoclg1f.mm"

theorem vtoclg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume vtoclg.1: |- ( x = A -> ( ph <-> ps ) )
  assume vtoclg.2: |- ph

  disjoint A x
  disjoint ps x
  assert |- ( A e. V -> ps )

  proof
    wph
    wps
    vx
    cA
    cV
    wps
    vx
    nfv
    vtoclg.1
    vtoclg.2
    vtoclg1f
end
