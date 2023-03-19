include "a1i.mm"
include "syl3c.mm"

theorem ee010
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee010.1: |- ph
  assume ee010.2: |- ( ps -> ch )
  assume ee010.3: |- th
  assume ee010.4: |- ( ph -> ( ch -> ( th -> ta ) ) )


  assert |- ( ps -> ta )

  proof
    wps
    wph
    wch
    wth
    wta
    wph
    wps
    ee010.1
    a1i
    ee010.2
    wth
    wps
    ee010.3
    a1i
    ee010.4
    syl3c
end
