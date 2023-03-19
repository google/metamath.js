include "wa.mm"
include "simpl.mm"
include "sylanl1.mm"

theorem adantllr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adantl2.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ( ph /\ ta ) /\ ps ) /\ ch ) -> th )

  proof
    wph
    wta
    wa
    wph
    wps
    wch
    wth
    wph
    wta
    simpl
    adantl2.1
    sylanl1
end
