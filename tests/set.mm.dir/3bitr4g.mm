include "syl5bb.mm"
include "syl6bbr.mm"

theorem 3bitr4g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitr4g.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitr4g.2: |- ( th <-> ps )
  assume 3bitr4g.3: |- ( ta <-> ch )


  assert |- ( ph -> ( th <-> ta ) )

  proof
    wph
    wth
    wch
    wta
    wth
    wps
    wph
    wch
    3bitr4g.2
    3bitr4g.1
    syl5bb
    3bitr4g.3
    syl6bbr
end
