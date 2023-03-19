include "nfv.mm"
include "eean.mm"

theorem eeanv
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y

  disjoint ph y
  disjoint ps x
  assert |- ( E. x E. y ( ph /\ ps ) <-> ( E. x ph /\ E. y ps ) )

  proof
    wph
    wps
    vx
    vy
    wph
    vy
    nfv
    wps
    vx
    nfv
    eean
end
