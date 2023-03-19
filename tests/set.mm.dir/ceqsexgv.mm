include "nfv.mm"
include "ceqsexg.mm"

theorem ceqsexgv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume ceqsexgv.1: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( A e. V -> ( E. x ( x = A /\ ph ) <-> ps ) )

  proof
    wph
    wps
    vx
    cA
    cV
    wps
    vx
    nfv
    ceqsexgv.1
    ceqsexg
end
