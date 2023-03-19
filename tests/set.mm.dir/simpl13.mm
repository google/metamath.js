include "w3a.mm"
include "simp13.mm"
include "adantr.mm"

theorem simpl13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wth
    wta
    w3a
    wch
    wet
    wph
    wps
    wch
    wth
    wta
    simp13
    adantr
end
