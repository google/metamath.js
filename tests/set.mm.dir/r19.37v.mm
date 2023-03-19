include "nfv.mm"
include "r19.37.mm"

theorem r19.37v
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A

  disjoint ph x
  assert |- ( E. x e. A ( ph -> ps ) -> ( ph -> E. x e. A ps ) )

  proof
    wph
    wps
    vx
    cA
    wph
    vx
    nfv
    r19.37
end
