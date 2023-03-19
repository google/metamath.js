include "wa.mm"
include "3com13.mm"
include "3adant1l.mm"

theorem 3adant3l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adant1l.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ps /\ ( ta /\ ch ) ) -> th )

  proof
    wta
    wch
    wa
    wps
    wph
    wth
    wch
    wps
    wph
    wth
    wta
    wph
    wps
    wch
    wth
    3adant1l.1
    3com13
    3adant1l
    3com13
end
