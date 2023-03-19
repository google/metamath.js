include "nfv.mm"
include "sbciegf.mm"

theorem sbcieg
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbcieg.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( A e. V -> ( [. A / x ]. ph <-> ps ) )

  proof
    wph
    wps
    vx
    cA
    cV
    wps
    vx
    nfv
    sbcieg.1
    sbciegf
end
