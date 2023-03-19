include "nfv.mm"
include "sbcgf.mm"

theorem sbcg
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint ph x
  assert |- ( A e. V -> ( [. A / x ]. ph <-> ph ) )

  proof
    wph
    vx
    cA
    cV
    wph
    vx
    nfv
    sbcgf
end
