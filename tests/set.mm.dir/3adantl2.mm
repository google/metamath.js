include "w3a.mm"
include "wa.mm"
include "3simpb.mm"
include "sylan.mm"

theorem 3adantl2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adantl.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ph /\ ta /\ ps ) /\ ch ) -> th )

  proof
    wph
    wta
    wps
    w3a
    wph
    wps
    wa
    wch
    wth
    wph
    wta
    wps
    3simpb
    3adantl.1
    sylan
end
