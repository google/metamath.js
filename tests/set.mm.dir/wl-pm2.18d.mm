include "wn.mm"
include "wi.mm"
include "ax-luk2.mm"
include "wl-syl.mm"

theorem wl-pm2.18d
  let wph: wff ph
  let wps: wff ps
  assume wl-pm2.18d.1: |- ( ph -> ( -. ps -> ps ) )


  assert |- ( ph -> ps )

  proof
    wph
    wps
    wn
    wps
    wi
    wps
    wl-pm2.18d.1
    wps
    ax-luk2
    wl-syl
end
