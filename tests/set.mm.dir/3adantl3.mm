include "w3a.mm"
include "wa.mm"
include "3simpa.mm"
include "sylan.mm"

theorem 3adantl3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adantl.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ph /\ ps /\ ta ) /\ ch ) -> th )

  proof
    wph
    wps
    wta
    w3a
    wph
    wps
    wa
    wch
    wth
    wph
    wps
    wta
    3simpa
    3adantl.1
    sylan
end
