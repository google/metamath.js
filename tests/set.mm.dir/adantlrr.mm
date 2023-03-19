include "wa.mm"
include "simpl.mm"
include "sylanl2.mm"

theorem adantlrr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adantl2.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ph /\ ( ps /\ ta ) ) /\ ch ) -> th )

  proof
    wps
    wta
    wa
    wph
    wps
    wch
    wth
    wps
    wta
    simpl
    adantl2.1
    sylanl2
end
