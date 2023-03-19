include "wi.mm"
include "syl6.mm"
include "mpdd.mm"

theorem syl6c
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume syl6c.1: |- ( ph -> ( ps -> ch ) )
  assume syl6c.2: |- ( ph -> ( ps -> th ) )
  assume syl6c.3: |- ( ch -> ( th -> ta ) )


  assert |- ( ph -> ( ps -> ta ) )

  proof
    wph
    wps
    wth
    wta
    syl6c.2
    wph
    wps
    wch
    wth
    wta
    wi
    syl6c.1
    syl6c.3
    syl6
    mpdd
end
