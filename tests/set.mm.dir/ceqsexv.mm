include "nfv.mm"
include "ceqsex.mm"

theorem ceqsexv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ceqsexv.1: |- A e. _V
  assume ceqsexv.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( E. x ( x = A /\ ph ) <-> ps )

  proof
    wph
    wps
    vx
    cA
    wps
    vx
    nfv
    ceqsexv.1
    ceqsexv.2
    ceqsex
end
