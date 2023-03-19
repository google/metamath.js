include "ex.mm"
include "e01.mm"

theorem e01an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e01an.1: |- ph
  assume e01an.2: |- (. ps ->. ch ).
  assume e01an.3: |- ( ( ph /\ ch ) -> th )


  assert |- (. ps ->. th ).

  proof
    wph
    wps
    wch
    wth
    e01an.1
    e01an.2
    wph
    wch
    wth
    e01an.3
    ex
    e01
end
