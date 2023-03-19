include "a1i.mm"
include "syl3c.mm"

theorem ee101
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ee101.1: |- ( ph -> ps )
  assume ee101.2: |- ch
  assume ee101.3: |- ( ph -> th )
  assume ee101.4: |- ( ps -> ( ch -> ( th -> ta ) ) )


  assert |- ( ph -> ta )

  proof
    wph
    wps
    wch
    wth
    wta
    ee101.1
    wch
    wph
    ee101.2
    a1i
    ee101.3
    ee101.4
    syl3c
end
