include "ex.mm"
include "ee30.mm"

theorem ee30an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ee30an.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume ee30an.2: |- ta
  assume ee30an.3: |- ( ( th /\ ta ) -> et )


  assert |- ( ph -> ( ps -> ( ch -> et ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    ee30an.1
    ee30an.2
    wth
    wta
    wet
    ee30an.3
    ex
    ee30
end
