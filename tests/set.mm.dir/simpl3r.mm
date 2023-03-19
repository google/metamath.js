include "wa.mm"
include "w3a.mm"
include "simp3r.mm"
include "adantr.mm"

theorem simpl3r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ch /\ th /\ ( ph /\ ps ) ) /\ ta ) -> ps )

  proof
    wch
    wth
    wph
    wps
    wa
    w3a
    wps
    wta
    wch
    wth
    wph
    wps
    simp3r
    adantr
end
