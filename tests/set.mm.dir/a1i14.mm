include "wi.mm"
include "a1dd.mm"
include "a1i.mm"

theorem a1i14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume a1i14.1: |- ( ps -> ( ch -> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wps
    wch
    wth
    wta
    wi
    wi
    wi
    wph
    wps
    wch
    wta
    wth
    a1i14.1
    a1dd
    a1i
end
