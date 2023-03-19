include "bitr4d.mm"

theorem 3bitr4rd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitr4d.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitr4d.2: |- ( ph -> ( th <-> ps ) )
  assume 3bitr4d.3: |- ( ph -> ( ta <-> ch ) )


  assert |- ( ph -> ( ta <-> th ) )

  proof
    wph
    wta
    wps
    wth
    wph
    wta
    wch
    wps
    3bitr4d.3
    3bitr4d.1
    bitr4d
    3bitr4d.2
    bitr4d
end
