include "nfv.mm"
include "moexex.mm"

theorem moexexv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  assert |- ( ( E* x ph /\ A. x E* y ps ) -> E* y E. x ( ph /\ ps ) )

  proof
    wph
    wps
    vx
    vy
    wph
    vy
    nfv
    moexex
end
