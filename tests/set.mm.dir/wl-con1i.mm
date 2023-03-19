include "wn.mm"
include "wl-pm2.21.mm"
include "wl-syl5.mm"
include "wl-pm2.18d.mm"

theorem wl-con1i
  let wph: wff ph
  let wps: wff ps
  assume wl-con1i.1: |- ( -. ph -> ps )


  assert |- ( -. ps -> ph )

  proof
    wps
    wn
    #
    wph
    wph
    wn
    wps
    @0
    wph
    wl-con1i.1
    wps
    wph
    wl-pm2.21
    wl-syl5
    wl-pm2.18d
end
