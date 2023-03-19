include "a1dd.mm"
include "ee33.mm"

theorem ee32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee32.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee32.2: |- ( ph -> ( ps -> ta ) )
  assume ee32.3: |- ( th -> ( ta -> et ) )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee32.1
    wph
    wps
    wta
    wch
    ee32.2
    a1dd
    ee32.3
    ee33
end
