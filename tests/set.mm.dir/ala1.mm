include "wi.mm"
include "ax-1.mm"
include "alimi.mm"

theorem ala1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( A. x ph -> A. x ( ps -> ph ) )

  proof
    wph
    wps
    wph
    wi
    vx
    wph
    wps
    ax-1
    alimi
end
