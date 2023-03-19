include "w3a.mm"
include "simp12.mm"
include "adantr.mm"

theorem simpl12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ( ph /\ ps /\ ch ) /\ th /\ ta ) /\ et ) -> ps )

  proof
    wph
    wps
    wch
    w3a
    wth
    wta
    w3a
    wps
    wet
    wph
    wps
    wch
    wth
    wta
    simp12
    adantr
end
