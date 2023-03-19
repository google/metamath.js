include "wi.mm"
include "a1d.mm"
include "a1dd.mm"
include "ee333.mm"

theorem ee123
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume ee123.1: |- ( ph -> ps )
  assume ee123.2: |- ( ph -> ( ch -> th ) )
  assume ee123.3: |- ( ph -> ( ch -> ( ta -> et ) ) )
  assume ee123.4: |- ( ps -> ( th -> ( et -> ze ) ) )


  assert |- ( ph -> ( ch -> ( ta -> ze ) ) )

  proof
    wph
    wch
    wta
    wps
    wth
    wet
    wze
    wph
    wta
    wps
    wi
    wch
    wph
    wps
    wta
    ee123.1
    a1d
    a1d
    wph
    wch
    wth
    wta
    ee123.2
    a1dd
    ee123.3
    ee123.4
    ee333
end
