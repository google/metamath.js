include "w3a.mm"
include "simp21.mm"
include "adantr.mm"

theorem simpl21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( th /\ ( ph /\ ps /\ ch ) /\ ta ) /\ et ) -> ph )

  proof
    wth
    wph
    wps
    wch
    w3a
    wta
    w3a
    wph
    wet
    wth
    wph
    wps
    wch
    wta
    simp21
    adantr
end
