include "nfv.mm"
include "moanim.mm"

theorem moanimv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x

  disjoint ph x
  assert |- ( E* x ( ph /\ ps ) <-> ( ph -> E* x ps ) )

  proof
    wph
    wps
    vx
    wph
    vx
    nfv
    moanim
end
