include "wa.mm"
include "simpr.mm"
include "sylanl1.mm"

theorem adantlll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adantl2.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ( ta /\ ph ) /\ ps ) /\ ch ) -> th )

  proof
    wta
    wph
    wa
    wph
    wps
    wch
    wth
    wta
    wph
    simpr
    adantl2.1
    sylanl1
end
