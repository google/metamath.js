include "w3a.mm"
include "wa.mm"
include "3simpb.mm"
include "sylan2.mm"

theorem 3adantr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adantr.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ( ps /\ ta /\ ch ) ) -> th )

  proof
    wps
    wta
    wch
    w3a
    wph
    wps
    wch
    wa
    wth
    wps
    wta
    wch
    3simpb
    3adantr.1
    sylan2
end
