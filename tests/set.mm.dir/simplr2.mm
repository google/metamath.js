include "w3a.mm"
include "wa.mm"
include "simpr2.mm"
include "adantr.mm"

theorem simplr2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( th /\ ( ph /\ ps /\ ch ) ) /\ ta ) -> ps )

  proof
    wth
    wph
    wps
    wch
    w3a
    wa
    wps
    wta
    wth
    wph
    wps
    wch
    simpr2
    adantr
end
