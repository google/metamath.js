include "wi.mm"
include "ax-1.mm"
include "eximi.mm"

theorem exa1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x


  assert |- ( E. x ph -> E. x ( ps -> ph ) )

  proof
    wph
    wps
    wph
    wi
    vx
    wph
    wps
    ax-1
    eximi
end
