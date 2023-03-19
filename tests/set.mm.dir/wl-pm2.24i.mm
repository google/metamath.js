include "wn.mm"
include "wi.mm"
include "ax-luk3.mm"
include "ax-mp.mm"

theorem wl-pm2.24i
  let wph: wff ph
  let wps: wff ps
  assume wl-pm2.24i.1: |- ph


  assert |- ( -. ph -> ps )

  proof
    wph
    wph
    wn
    wps
    wi
    wl-pm2.24i.1
    wph
    wps
    ax-luk3
    ax-mp
end
