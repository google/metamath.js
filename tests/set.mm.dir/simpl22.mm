include "w3a.mm"
include "simp22.mm"
include "adantr.mm"

theorem simpl22
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ps )

  proof
    wth
    wph
    wps
    wch
    w3a
    wta
    w3a
    wps
    wet
    wth
    wph
    wps
    wch
    wta
    simp22
    adantr
end
