include "a1i.mm"
include "syl3c.mm"

theorem ee110
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee110.1: |- ( ph -> ps )
  assume ee110.2: |- ( ph -> ch )
  assume ee110.3: |- th
  assume ee110.4: |- ( ps -> ( ch -> ( th -> ta ) ) )


  assert |- ( ph -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    ee110.1
    ee110.2
    wth
    wph
    ee110.3
    a1i
    ee110.4
    syl3c
end
