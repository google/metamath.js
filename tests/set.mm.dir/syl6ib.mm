include "biimpi.mm"
include "syl6.mm"

theorem syl6ib
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume syl6ib.1: |- ( ph -> ( ps -> ch ) )
  assume syl6ib.2: |- ( ch <-> th )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    syl6ib.1
    wch
    wth
    syl6ib.2
    biimpi
    syl6
end
