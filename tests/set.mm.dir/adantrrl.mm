include "wa.mm"
include "simpr.mm"
include "sylanr2.mm"

theorem adantrrl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adantr2.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ( ps /\ ( ta /\ ch ) ) ) -> th )

  proof
    wta
    wch
    wa
    wph
    wps
    wch
    wth
    wta
    wch
    simpr
    adantr2.1
    sylanr2
end
