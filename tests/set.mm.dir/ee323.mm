include "a1dd.mm"
include "ee333.mm"

theorem ee323
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  assume ee323.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee323.2: |- ( ph -> ( ps -> ta ) )
  assume ee323.3: |- ( ph -> ( ps -> ( ch -> et ) ) )
  assume ee323.4: |- ( th -> ( ta -> ( et -> ze ) ) )


  assert |- ( ph -> ( ps -> ( ch -> ze ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    ee323.1
    wph
    wps
    wta
    wch
    ee323.2
    a1dd
    ee323.3
    ee323.4
    ee333
end
