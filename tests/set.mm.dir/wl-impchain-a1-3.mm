include "wi.mm"
include "wl-impchain-a1-2.mm"
include "wl-impchain-com-2.3.mm"

theorem wl-impchain-a1-3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume wl-impchain-a1-3.a: |- ( ph -> ( ps -> ch ) )


  assert |- ( ph -> ( ps -> ( th -> ch ) ) )

  proof
    wch
    wps
    wth
    wph
    wph
    wps
    wch
    wi
    wth
    wl-impchain-a1-3.a
    wl-impchain-a1-2
    wl-impchain-com-2.3
end
