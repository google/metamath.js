include "wn.mm"
include "wi.mm"
include "pm2.27.mm"
include "con2d.mm"

theorem pm3.2im
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> -. ( ph -> -. ps ) ) )

  proof
    wph
    wph
    wps
    wn
    #
    wi
    wps
    wph
    @0
    pm2.27
    con2d
end
