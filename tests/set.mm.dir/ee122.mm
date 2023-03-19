include "a1d.mm"
include "ee222.mm"

theorem ee122
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee122.1: |- ( ph -> ps )
  assume ee122.2: |- ( ph -> ( ch -> th ) )
  assume ee122.3: |- ( ph -> ( ch -> ta ) )
  assume ee122.4: |- ( ps -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ch -> et ) )

  proof
    wph
    wch
    wps
    wth
    wta
    wet
    wph
    wps
    wch
    ee122.1
    a1d
    ee122.2
    ee122.3
    ee122.4
    ee222
end
