include "nfv.mm"
include "ceqsal.mm"

theorem ceqsalv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  assume ceqsalv.1: |- A e. _V
  assume ceqsalv.2: |- ( x = A -> ( ph <-> ps ) )

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
    ceqsalv.1
    ceqsalv.2
    ceqsal
end
