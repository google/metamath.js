include "wa.mm"
include "simpl.mm"
include "sylanr2.mm"

theorem adantrrr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adantr2.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ( ps /\ ( ch /\ ta ) ) ) -> th )

  proof
    wch
    wta
    wa
    wph
    wps
    wch
    wth
    wch
    wta
    simpl
    adantr2.1
    sylanr2
end
