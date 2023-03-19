include "ex.mm"
include "ee33.mm"

theorem ee33an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee33an.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee33an.2: |- ( ph -> ( ps -> ( ch -> ta ) ) )
  assume ee33an.3: |- ( ( th /\ ta ) -> et )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee33an.1
    ee33an.2
    wth
    wta
    wet
    ee33an.3
    ex
    ee33
end
