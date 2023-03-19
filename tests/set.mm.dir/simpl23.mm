include "w3a.mm"
include "simp23.mm"
include "adantr.mm"

theorem simpl23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ch )

  proof
    wth
    wph
    wps
    wch
    w3a
    wta
    w3a
    wch
    wet
    wth
    wph
    wps
    wch
    wta
    simp23
    adantr
end
