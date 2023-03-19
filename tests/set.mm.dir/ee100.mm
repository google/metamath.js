include "a1i.mm"
include "syl3c.mm"

theorem ee100
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee100.1: |- ( ph -> ps )
  assume ee100.2: |- ch
  assume ee100.3: |- th
  assume ee100.4: |- ( ps -> ( ch -> ( th -> ta ) ) )


  assert |- ( ph -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    ee100.1
    wch
    wph
    ee100.2
    a1i
    wth
    wph
    ee100.3
    a1i
    ee100.4
    syl3c
end
