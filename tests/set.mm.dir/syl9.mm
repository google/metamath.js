include "wi.mm"
include "a1i.mm"
include "syl5d.mm"

theorem syl9
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
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
