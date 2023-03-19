include "a1d.mm"
include "ee222.mm"

theorem ee211
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee211.1: |- ( ph -> ( ps -> ch ) )
  assume ee211.2: |- ( ph -> th )
  assume ee211.3: |- ( ph -> ta )
  assume ee211.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- ( ph -> ( ps -> et ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee211.1
    wph
    wth
    wps
    ee211.2
    a1d
    wph
    wta
    wps
    ee211.3
    a1d
    ee211.4
    ee222
end
