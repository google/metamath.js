include "nfv.mm"
include "nfvd.mm"
include "sbciedf.mm"

theorem sbcied
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cV: class V
  assume sbcied.1: |- ( ph -> A e. V )
  assume sbcied.2: |- ( ( ph /\ x = A ) -> ( ps <-> ch ) )

  disjoint A x
  disjoint ph x
  disjoint ch x
  assert |- ( ph -> ( [. A / x ]. ps <-> ch ) )

  proof
    wph
    wps
    wch
    vx
    cA
    cV
    sbcied.1
    sbcied.2
    wph
    vx
    nfv
    wph
    wch
    vx
    nfvd
    sbciedf
end
