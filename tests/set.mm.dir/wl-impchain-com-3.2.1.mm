include "wi.mm"
include "wl-impchain-com-2.3.mm"
include "wl-impchain-com-1.2.mm"

theorem wl-impchain-com-3.2.1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-impchain-com-3.2.1.h1: |- ( th -> ( ch -> ( ps -> ph ) ) )


  assert |- ( ps -> ( th -> ( ch -> ph ) ) )

  proof
    wch
    wph
    wi
    wps
    wth
    wph
    wps
    wch
    wth
    wl-impchain-com-3.2.1.h1
    wl-impchain-com-2.3
    wl-impchain-com-1.2
end
