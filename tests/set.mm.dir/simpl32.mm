include "w3a.mm"
include "simp32.mm"
include "adantr.mm"

theorem simpl32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( th /\ ta /\ ( ph /\ ps /\ ch ) ) /\ et ) -> ps )

  proof
    wth
    wta
    wph
    wps
    wch
    w3a
    w3a
    wps
    wet
    wth
    wta
    wph
    wps
    wch
    simp32
    adantr
end
