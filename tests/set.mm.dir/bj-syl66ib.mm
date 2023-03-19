include "syl6.mm"
include "syl6ib.mm"

theorem bj-syl66ib
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume bj-syl66ib.1: |- ( ph -> ( ps -> th ) )
  assume bj-syl66ib.2: |- ( th -> ta )
  assume bj-syl66ib.3: |- ( ta <-> ch )


  assert |- ( ph -> ( ps -> ch ) )

  proof
    wph
    wps
    wta
    wch
    wph
    wps
    wth
    wta
    bj-syl66ib.1
    bj-syl66ib.2
    syl6
    bj-syl66ib.3
    syl6ib
end
