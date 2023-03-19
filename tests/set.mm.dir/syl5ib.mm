include "biimpd.mm"
include "syl5.mm"

theorem syl5ib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syl5ib.1: |- ( ph -> ps )
  assume syl5ib.2: |- ( ch -> ( ps <-> th ) )


  assert |- ( ch -> ( ph -> th ) )

  proof
    wph
    wps
    wch
    wth
    syl5ib.1
    wch
    wps
    wth
    syl5ib.2
    biimpd
    syl5
end
