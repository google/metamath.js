include "w3a.mm"
include "wa.mm"
include "3simpa.mm"
include "sylan2.mm"

theorem 3adantr3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume 3adantr.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ( ps /\ ch /\ ta ) ) -> th )

  proof
    wps
    wch
    wta
    w3a
    wph
    wps
    wch
    wa
    wth
    wps
    wch
    wta
    3simpa
    3adantr.1
    sylan2
end
