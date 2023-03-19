include "wa.mm"
include "3com12.mm"
include "3adant1l.mm"

theorem 3adant2l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adant1l.1: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- ( ( ph /\ ( ta /\ ps ) /\ ch ) -> th )

  proof
    wta
    wps
    wa
    wph
    wch
    wth
    wps
    wph
    wch
    wth
    wta
    wph
    wps
    wch
    wth
    3adant1l.1
    3com12
    3adant1l
    3com12
end
