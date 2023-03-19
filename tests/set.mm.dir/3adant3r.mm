include "wa.mm"
include "3com13.mm"
include "3adant1r.mm"

theorem 3adant3r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adant1l.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ps /\ ( ch /\ ta ) ) -> th )

  proof
    wch
    wta
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
    3adant1r
    3com13
end
