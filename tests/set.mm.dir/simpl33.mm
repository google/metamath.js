include "w3a.mm"
include "simp33.mm"
include "adantr.mm"

theorem simpl33
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ch )

  proof
    wth
    wta
    wph
    wps
    wch
    w3a
    w3a
    wch
    wet
    wth
    wta
    wph
    wps
    wch
    simp33
    adantr
end
