include "wi.mm"
include "wl-pm2.27.mm"
include "wl-syl5.mm"

theorem wl-com12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-com12.1: |- ( ph -> ( ps -> ch ) )


  assert |- ( ps -> ( ph -> ch ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wch
    wl-com12.1
    wps
    wch
    wl-pm2.27
    wl-syl5
end
