include "syl6.mm"
include "syl5.mm"

theorem syl56
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syl56.1: |- ( ph -> ps )
  assume syl56.2: |- ( ch -> ( ps -> th ) )
  assume syl56.3: |- ( th -> ta )


  assert |- ( ch -> ( ph -> ta ) )

  proof
    wph
    wps
    wch
    wta
    syl56.1
    wch
    wps
    wth
    wta
    syl56.2
    syl56.3
    syl6
    syl5
end
