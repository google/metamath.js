include "sylibd.mm"
include "sylbird.mm"

theorem 3imtr3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3imtr3d.1: |- ( ph -> ( ps -> ch ) )
  assume 3imtr3d.2: |- ( ph -> ( ps <-> th ) )
  assume 3imtr3d.3: |- ( ph -> ( ch <-> ta ) )


  assert |- ( ph -> ( th -> ta ) )

  proof
    wph
    wth
    wps
    wta
    3imtr3d.2
    wph
    wps
    wch
    wta
    3imtr3d.1
    3imtr3d.3
    sylibd
    sylbird
end
