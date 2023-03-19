include "wi.mm"
include "wl-impchain-com-1.2.mm"
include "wl-pm2.04.mm"
include "wl-impchain-mp-1.mm"

theorem wl-impchain-com-1.3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-impchain-com-1.3.h1: |- ( th -> ( ch -> ( ps -> ph ) ) )


  assert |- ( ps -> ( ch -> ( th -> ph ) ) )

  proof
    wth
    wph
    wi
    #
    wps
    wch
    wps
    @0
    wi
    wth
    wps
    wph
    wi
    #
    wi
    wch
    @1
    wch
    wth
    wl-impchain-com-1.3.h1
    wl-impchain-com-1.2
    wth
    wps
    wph
    wl-pm2.04
    wl-impchain-mp-1
    wl-impchain-com-1.2
end
