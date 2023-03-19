include "wi.mm"
include "wl-impchain-com-1.3.mm"
include "wl-pm2.04.mm"
include "wl-impchain-mp-2.mm"

theorem wl-impchain-com-1.4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wet: wff et
  assume wl-impchain-com-1.4.h1: |- ( et -> ( th -> ( ch -> ( ps -> ph ) ) ) )


  assert |- ( ps -> ( th -> ( ch -> ( et -> ph ) ) ) )

  proof
    wet
    wph
    wi
    #
    wps
    wth
    wch
    wps
    @0
    wi
    wet
    wps
    wph
    wi
    #
    wi
    wth
    wch
    @1
    wch
    wth
    wet
    wl-impchain-com-1.4.h1
    wl-impchain-com-1.3
    wet
    wps
    wph
    wl-pm2.04
    wl-impchain-mp-2
    wl-impchain-com-1.3
end
