include "wi.mm"
include "wn.mm"
include "wl-pm2.21.mm"
include "wl-a1d.mm"
include "wl-imim2.mm"
include "wl-ja.mm"

theorem wl-ax2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ph -> ps ) -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    wph
    wps
    wi
    #
    wph
    wch
    wi
    #
    wi
    wph
    wn
    @1
    @0
    wph
    wch
    wl-pm2.21
    wl-a1d
    wps
    wch
    wph
    wl-imim2
    wl-ja
end
