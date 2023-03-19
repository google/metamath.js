include "nfv.mm"
include "bj-ceqsal.mm"

theorem bj-ceqsalv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume bj-ceqsalv.1: |- A e. _V
  assume bj-ceqsalv.2: |- ( x = A -> ( ph <-> ps ) )

  disjoint A x
  disjoint ps x
  assert |- ( A. x ( x = A -> ph ) <-> ps )

  proof
    wph
    wps
    vx
    cA
    wps
    vx
    nfv
    bj-ceqsalv.1
    bj-ceqsalv.2
    bj-ceqsal
end
