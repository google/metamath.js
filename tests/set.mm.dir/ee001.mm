include "a1i.mm"
include "syl3c.mm"

theorem ee001
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee001.1: |- ph
  assume ee001.2: |- ps
  assume ee001.3: |- ( ch -> th )
  assume ee001.4: |- ( ph -> ( ps -> ( th -> ta ) ) )


  assert |- ( ch -> ta )

  proof
    wch
    wph
    wps
    wth
    wta
    wph
    wch
    ee001.1
    a1i
    wps
    wch
    ee001.2
    a1i
    ee001.3
    ee001.4
    syl3c
end
