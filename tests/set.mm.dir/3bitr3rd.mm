include "bitr3d.mm"

theorem 3bitr3rd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitr3d.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitr3d.2: |- ( ph -> ( ps <-> th ) )
  assume 3bitr3d.3: |- ( ph -> ( ch <-> ta ) )


  assert |- ( ph -> ( ta <-> th ) )

  proof
    wph
    wch
    wta
    wth
    3bitr3d.3
    wph
    wps
    wch
    wth
    3bitr3d.1
    3bitr3d.2
    bitr3d
    bitr3d
end
