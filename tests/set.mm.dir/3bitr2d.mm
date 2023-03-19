include "bitr4d.mm"
include "bitrd.mm"

theorem 3bitr2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitr2d.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitr2d.2: |- ( ph -> ( th <-> ch ) )
  assume 3bitr2d.3: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ps <-> ta ) )

  proof
    wph
    wps
    wth
    wta
    wph
    wps
    wch
    wth
    3bitr2d.1
    3bitr2d.2
    bitr4d
    3bitr2d.3
    bitrd
end
