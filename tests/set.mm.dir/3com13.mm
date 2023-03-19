include "w3a.mm"
include "3anrev.mm"
include "sylbi.mm"

theorem 3com13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ch /\ ps /\ ph ) -> th )

  proof
    wch
    wps
    wph
    w3a
    wph
    wps
    wch
    w3a
    wth
    wch
    wps
    wph
    3anrev
    3exp.1
    sylbi
end
