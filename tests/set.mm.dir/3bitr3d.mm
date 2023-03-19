include "bitr3d.mm"
include "bitrd.mm"

theorem 3bitr3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitr3d.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitr3d.2: |- ( ph -> ( ps <-> th ) )
  assume 3bitr3d.3: |- ( ph -> ( ch <-> ta ) )


  assert |- ( ph -> ( th <-> ta ) )

  proof
    wph
    wth
    wch
    wta
    wph
    wps
    wth
    wch
    3bitr3d.2
    3bitr3d.1
    bitr3d
    3bitr3d.3
    bitrd
end
