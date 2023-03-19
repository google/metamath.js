include "w3a.mm"
include "3ancoma.mm"
include "sylbi.mm"

theorem 3com12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3exp.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ps /\ ph /\ ch ) -> th )

  proof
    wps
    wph
    wch
    w3a
    wph
    wps
    wch
    w3a
    wth
    wps
    wph
    wch
    3ancoma
    3exp.1
    sylbi
end
