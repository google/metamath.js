include "wa.mm"
include "simpr.mm"
include "sylanr1.mm"

theorem adantrll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adantr2.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ( ( ta /\ ps ) /\ ch ) ) -> th )

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
    adantr2.1
    sylanr1
end
