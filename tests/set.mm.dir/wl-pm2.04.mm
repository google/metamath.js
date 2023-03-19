include "wi.mm"
include "wl-ax1.mm"
include "wl-ax2.mm"
include "wl-syl5.mm"

theorem wl-pm2.04
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) )

  proof
    wps
    wph
    wps
    wi
    wph
    wps
    wch
    wi
    wi
    wph
    wch
    wi
    wps
    wph
    wl-ax1
    wph
    wps
    wch
    wl-ax2
    wl-syl5
end
