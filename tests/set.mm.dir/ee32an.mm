include "a1dd.mm"
include "ee33an.mm"

theorem ee32an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee32an.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee32an.2: |- ( ph -> ( ps -> ta ) )
  assume ee32an.3: |- ( ( th /\ ta ) -> et )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee32an.1
    wph
    wps
    wta
    wch
    ee32an.2
    a1dd
    ee32an.3
    ee33an
end
