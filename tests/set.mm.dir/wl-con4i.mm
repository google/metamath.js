include "wn.mm"
include "ax-luk3.mm"
include "wl-syl5.mm"
include "wl-pm2.18d.mm"

theorem wl-con4i
  let wph: wff ph
  let wps: wff ps
  assume wl-con4i.1: |- ( -. ph -> -. ps )


  assert |- ( ps -> ph )

  proof
    wps
    wph
    wph
    wn
    wps
    wn
    wps
    wph
    wl-con4i.1
    wps
    wph
    ax-luk3
    wl-syl5
    wl-pm2.18d
end
