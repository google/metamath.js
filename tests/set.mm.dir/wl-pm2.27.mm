include "wi.mm"
include "wn.mm"
include "wl-ax1.mm"
include "ax-luk1.mm"
include "wl-syl.mm"
include "ax-luk2.mm"
include "wl-syl6.mm"

theorem wl-pm2.27
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ( ph -> ps ) -> ps ) )

  proof
    wph
    wph
    wps
    wi
    #
    wps
    wn
    #
    wps
    wi
    #
    wps
    wph
    @1
    wph
    wi
    @0
    @2
    wi
    wph
    @1
    wl-ax1
    @1
    wph
    wps
    ax-luk1
    wl-syl
    wps
    ax-luk2
    wl-syl6
end
