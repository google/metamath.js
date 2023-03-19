include "bitr2d.mm"
include "bitr3d.mm"

theorem 3bitrrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitrd.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitrd.2: |- ( ph -> ( ch <-> th ) )
  assume 3bitrd.3: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ta <-> ps ) )

  proof
    wph
    wth
    wta
    wps
    3bitrd.3
    wph
    wps
    wch
    wth
    3bitrd.1
    3bitrd.2
    bitr2d
    bitr3d
end
