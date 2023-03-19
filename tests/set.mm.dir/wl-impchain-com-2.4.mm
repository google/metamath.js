include "wi.mm"
include "wl-impchain-com-1.2.mm"
include "wl-impchain-com-1.4.mm"

theorem wl-impchain-com-2.4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wet: wff et
  assume wl-impchain-com-2.4.h1: |- ( et -> ( th -> ( ch -> ( ps -> ph ) ) ) )


  assert |- ( et -> ( ps -> ( ch -> ( th -> ph ) ) ) )

  proof
    wch
    wth
    wph
    wi
    wi
    wet
    wps
    wph
    wps
    wch
    wet
    wth
    wch
    wps
    wph
    wi
    wi
    wth
    wet
    wl-impchain-com-2.4.h1
    wl-impchain-com-1.2
    wl-impchain-com-1.4
    wl-impchain-com-1.2
end
