include "wi.mm"
include "a1d.mm"
include "syldd.mm"

theorem syl5d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syl5d.1: |- ( ph -> ( ps -> ch ) )
  assume syl5d.2: |- ( ph -> ( th -> ( ch -> ta ) ) )


  assert |- ( ph -> ( th -> ( ps -> ta ) ) )

  proof
    wph
    wth
    wps
    wch
    wta
    wph
    wps
    wch
    wi
    wth
    syl5d.1
    a1d
    syl5d.2
    syldd
end
