include "w3a.mm"
include "wa.mm"
include "simpr1.mm"
include "adantr.mm"

theorem simplr1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ph )

  proof
    wth
    wph
    wps
    wch
    w3a
    wa
    wph
    wta
    wth
    wph
    wps
    wch
    simpr1
    adantr
end
