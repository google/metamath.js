include "a1i.mm"
include "a1d.mm"
include "a1dd.mm"
include "ee33.mm"

theorem ee03
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee03.1: |- ph
  assume ee03.2: |- ( ps -> ( ch -> ( th -> ta ) ) )
  assume ee03.3: |- ( ph -> ( ta -> et ) )


  assert |- ( ps -> ( ch -> ( th -> et ) ) )

  proof
    wps
    wch
    wth
    wph
    wta
    wet
    wps
    wch
    wph
    wth
    wps
    wph
    wch
    wph
    wps
    ee03.1
    a1i
    a1d
    a1dd
    ee03.2
    ee03.3
    ee33
end
