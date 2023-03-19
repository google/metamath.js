include "sylancr.mm"

theorem ee01an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ee01an.1: |- ph
  assume ee01an.2: |- ( ps -> ch )
  assume ee01an.3: |- ( ( ph /\ ch ) -> th )


  assert |- ( ps -> th )

  proof
    wps
    wph
    wch
    wth
    ee01an.1
    ee01an.2
    ee01an.3
    sylancr
end
