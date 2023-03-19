include "wi.mm"
include "wl-impchain-com-1.1.mm"
include "wl-pm2.04.mm"
include "wl-impchain-mp-0.mm"

theorem wl-impchain-com-1.2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume wl-impchain-com.1.2.a: |- ( ch -> ( ps -> ph ) )


  assert |- ( ps -> ( ch -> ph ) )

  proof
    wch
    wph
    wi
    #
    wps
    wps
    @0
    wi
    wch
    wps
    wph
    wi
    #
    wi
    @1
    wch
    wl-impchain-com.1.2.a
    wl-impchain-com-1.1
    wch
    wps
    wph
    wl-pm2.04
    wl-impchain-mp-0
    wl-impchain-com-1.1
end
