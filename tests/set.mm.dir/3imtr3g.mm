include "syl5bir.mm"
include "syl6ib.mm"

theorem 3imtr3g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
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
