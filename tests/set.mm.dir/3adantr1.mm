include "w3a.mm"
include "wa.mm"
include "3simpc.mm"
include "sylan2.mm"

theorem 3adantr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adantr.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ( ta /\ ps /\ ch ) ) -> th )

  proof
    wta
    wps
    wch
    w3a
    wph
    wps
    wch
    wa
    wth
    wta
    wps
    wch
    3simpc
    3adantr.1
    sylan2
end
