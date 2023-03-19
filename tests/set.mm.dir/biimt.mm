include "wi.mm"
include "ax-1.mm"
include "pm2.27.mm"
include "impbid2.mm"

theorem biimt
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps <-> ( ph -> ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wi
    wps
    wph
    ax-1
    wph
    wps
    pm2.27
    impbid2
end
