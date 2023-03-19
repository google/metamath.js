include "wi.mm"
include "a1i.mm"
include "syl5d.mm"

theorem syl9
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl9.1: |- ( ph -> ( ps -> ch ) )
  assume syl9.2: |- ( th -> ( ch -> ta ) )


  assert |- ( ph -> ( th -> ( ps -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    syl9.1
    wth
    wch
    wta
    wi
    wi
    wph
    syl9.2
    a1i
    syl5d
end
