include "wi.mm"
include "wl-imim2i.mm"
include "wl-impchain-mp-1.mm"

theorem wl-impchain-mp-2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-impchain-mp-2.a: |- ( th -> ( ch -> ps ) )
  assume wl-impchain-mp-2.b: |- ( ps -> ph )


  assert |- ( th -> ( ch -> ph ) )

  proof
    wch
    wph
    wi
    wch
    wps
    wi
    wth
    wl-impchain-mp-2.a
    wps
    wph
    wch
    wl-impchain-mp-2.b
    wl-imim2i
    wl-impchain-mp-1
end
