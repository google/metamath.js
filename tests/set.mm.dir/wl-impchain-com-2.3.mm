include "wi.mm"
include "wl-impchain-com-1.2.mm"
include "wl-impchain-com-1.3.mm"

theorem wl-impchain-com-2.3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-impchain-com-2.3.h1: |- ( th -> ( ch -> ( ps -> ph ) ) )


  assert |- ( th -> ( ps -> ( ch -> ph ) ) )

  proof
    wch
    wph
    wi
    wth
    wps
    wph
    wps
    wth
    wch
    wps
    wph
    wi
    wch
    wth
    wl-impchain-com-2.3.h1
    wl-impchain-com-1.2
    wl-impchain-com-1.3
    wl-impchain-com-1.2
end
