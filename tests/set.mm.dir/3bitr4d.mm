include "bitr4d.mm"
include "bitrd.mm"

theorem 3bitr4d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitr4d.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitr4d.2: |- ( ph -> ( th <-> ps ) )
  assume 3bitr4d.3: |- ( ph -> ( ta <-> ch ) )


  assert |- ( ph -> ( th <-> ta ) )

  proof
    wph
    wth
    wps
    wta
    3bitr4d.2
    wph
    wps
    wch
    wta
    3bitr4d.1
    3bitr4d.3
    bitr4d
    bitrd
end
