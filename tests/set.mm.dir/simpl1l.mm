include "wa.mm"
include "w3a.mm"
include "simp1l.mm"
include "adantr.mm"

theorem simpl1l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ph )

  proof
    wph
    wps
    wa
    wch
    wth
    w3a
    wph
    wta
    wph
    wps
    wch
    wth
    simp1l
    adantr
end
