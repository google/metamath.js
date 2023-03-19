include "wn.mm"
include "wl-pm2.24i.mm"
include "wl-con4i.mm"

theorem wl-a1i
  let wph: wff ph
  let wps: wff ps
  assume wl-a1i.1: |- ph


  assert |- ( ps -> ph )

  proof
    wph
    wps
    wph
    wps
    wn
    wl-a1i.1
    wl-pm2.24i
    wl-con4i
end
