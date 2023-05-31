include "wi.mm"
include "a1d.mm"
include "syldd.mm"

theorem syl6d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syl6d.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume syl6d.2: |- ( ph -> ( th -> ta ) )


  assert |- ( ph -> ( ps -> ( ch -> ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    syl6d.1
    wph
    wth
    wta
    wi
    wps
    syl6d.2
    a1d
    syldd
end
