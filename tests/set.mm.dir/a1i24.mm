include "wi.mm"
include "a1dd.mm"
include "a1d.mm"

theorem a1i24
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume a1i24.1: |- ( ph -> ( ch -> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) )

  proof
    wph
    wch
    wth
    wta
    wi
    wi
    wps
    wph
    wch
    wta
    wth
    a1i24.1
    a1dd
    a1d
end
