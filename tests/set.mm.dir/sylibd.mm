include "biimpd.mm"
include "syld.mm"

theorem sylibd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylibd.1: |- ( ph -> ( ps -> ch ) )
  assume sylibd.2: |- ( ph -> ( ch <-> th ) )


  assert |- ( ph -> ( ps -> th ) )

  proof
    wph
    wps
    wch
    wth
    sylibd.1
    wph
    wch
    wth
    sylibd.2
    biimpd
    syld
end
