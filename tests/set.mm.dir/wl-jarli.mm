include "wn.mm"
include "wi.mm"
include "pm2.21.mm"
include "syl.mm"

theorem wl-jarli
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-jarli.1: |- ( ( ph -> ps ) -> ch )


  assert |- ( -. ph -> ch )

  proof
    wph
    wn
    wph
    wps
    wi
    wch
    wph
    wps
    pm2.21
    wl-jarli.1
    syl
end
