include "wa.mm"
include "w3a.mm"
include "simp3l.mm"
include "adantr.mm"

theorem simpl3l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ph )

  proof
    wch
    wth
    wph
    wps
    wa
    w3a
    wph
    wta
    wch
    wth
    wph
    wps
    simp3l
    adantr
end
