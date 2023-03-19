include "w3a.mm"
include "3imp.mm"
include "syl3c.mm"
include "3exp.mm"

theorem ee333
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume ee333.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee333.2: |- ( ph -> ( ps -> ( ch -> ta ) ) )
  assume ee333.3: |- ( ph -> ( ps -> ( ch -> et ) ) )
  assume ee333.4: |- ( th -> ( ta -> ( et -> ze ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ze ) ) )

  proof
    wph
    wps
    wch
    wze
    wph
    wps
    wch
    w3a
    wth
    wta
    wet
    wze
    wph
    wps
    wch
    wth
    ee333.1
    3imp
    wph
    wps
    wch
    wta
    ee333.2
    3imp
    wph
    wps
    wch
    wet
    ee333.3
    3imp
    ee333.4
    syl3c
    3exp
end
