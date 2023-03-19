include "wa.mm"
include "w3a.mm"
include "simp2l.mm"
include "adantr.mm"

theorem simpl2l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ph )

  proof
    wch
    wph
    wps
    wa
    wth
    w3a
    wph
    wta
    wch
    wph
    wps
    wth
    simp2l
    adantr
end
