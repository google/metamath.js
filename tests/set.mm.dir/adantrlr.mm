include "wa.mm"
include "simpl.mm"
include "sylanr1.mm"

theorem adantrlr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adantr2.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ( ( ps /\ ta ) /\ ch ) ) -> th )

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
    adantr2.1
    sylanr1
end
