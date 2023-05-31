include "syl5bir.mm"
include "syl6ib.mm"

theorem 3imtr3g
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume 3imtr3g.1: |- ( ph -> ( ps -> ch ) )
  assume 3imtr3g.2: |- ( ps <-> th )
  assume 3imtr3g.3: |- ( ch <-> ta )


  assert |- ( ph -> ( th -> ta ) )

  proof
    wph
    wth
    wch
    wta
    wth
    wps
    wph
    wch
    3imtr3g.2
    3imtr3g.1
    syl5bir
    3imtr3g.3
    syl6ib
end
