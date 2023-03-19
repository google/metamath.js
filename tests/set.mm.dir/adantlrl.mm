include "wa.mm"
include "simpr.mm"
include "sylanl2.mm"

theorem adantlrl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adantl2.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ph /\ ( ta /\ ps ) ) /\ ch ) -> th )

  proof
    wta
    wps
    wa
    wph
    wps
    wch
    wth
    wta
    wps
    simpr
    adantl2.1
    sylanl2
end
