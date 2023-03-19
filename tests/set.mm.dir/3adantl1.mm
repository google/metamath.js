include "w3a.mm"
include "wa.mm"
include "3simpc.mm"
include "sylan.mm"

theorem 3adantl1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adantl.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ta /\ ph /\ ps ) /\ ch ) -> th )

  proof
    wta
    wph
    wps
    w3a
    wph
    wps
    wa
    wch
    wth
    wta
    wph
    wps
    3simpc
    3adantl.1
    sylan
end
