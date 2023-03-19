include "syl5bbr.mm"
include "syl6bb.mm"

theorem 3bitr3g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3bitr3g.1: |- ( ph -> ( ps <-> ch ) )
  assume 3bitr3g.2: |- ( ps <-> th )
  assume 3bitr3g.3: |- ( ch <-> ta )


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
    3bitr3g.2
    3bitr3g.1
    syl5bbr
    3bitr3g.3
    syl6bb
end
