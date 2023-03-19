include "nf5i.mm"
include "sbciegf.mm"

theorem bnj1464
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume bnj1464.1: |- ( ps -> A. x ps )
  assume bnj1464.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint V x
  assert |- ( A e. V -> ( [. A / x ]. ph <-> ps ) )

  proof
    wph
    wps
    vx
    cA
    cV
    wps
    vx
    bnj1464.1
    nf5i
    bnj1464.2
    sbciegf
end
