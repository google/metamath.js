include "w3a.mm"
include "simp11.mm"
include "adantr.mm"

theorem simpl11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ph )

  proof
    wph
    wps
    wch
    w3a
    wth
    wta
    w3a
    wph
    wet
    wph
    wps
    wch
    wth
    wta
    simp11
    adantr
end
