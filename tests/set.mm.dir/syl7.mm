include "wi.mm"
include "a1i.mm"
include "syl5d.mm"

theorem syl7
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syl7.1: |- ( ph -> ps )
  assume syl7.2: |- ( ch -> ( th -> ( ps -> ta ) ) )


  assert |- ( ch -> ( th -> ( ph -> ta ) ) )

  proof
    wch
    wph
    wps
    wth
    wta
    wph
    wps
    wi
    wch
    syl7.1
    a1i
    syl7.2
    syl5d
end
