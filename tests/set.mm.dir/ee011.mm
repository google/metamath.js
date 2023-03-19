include "a1i.mm"
include "syl3c.mm"

theorem ee011
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee011.1: |- ph
  assume ee011.2: |- ( ps -> ch )
  assume ee011.3: |- ( ps -> th )
  assume ee011.4: |- ( ph -> ( ch -> ( th -> ta ) ) )


  assert |- ( ps -> ta )

  proof
    wps
    wph
    wch
    wth
    wta
    wph
    wps
    ee011.1
    a1i
    ee011.2
    ee011.3
    ee011.4
    syl3c
end
