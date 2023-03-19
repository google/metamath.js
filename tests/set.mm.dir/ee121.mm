include "a1d.mm"
include "ee222.mm"

theorem ee121
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee121.1: |- ( ph -> ps )
  assume ee121.2: |- ( ph -> ( ch -> th ) )
  assume ee121.3: |- ( ph -> ta )
  assume ee121.4: |- ( ps -> ( th -> ( ta -> et ) ) )


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
    ee121.1
    a1d
    ee121.2
    wph
    wta
    wch
    ee121.3
    a1d
    ee121.4
    ee222
end
