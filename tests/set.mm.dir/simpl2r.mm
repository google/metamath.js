include "wa.mm"
include "w3a.mm"
include "simp2r.mm"
include "adantr.mm"

theorem simpl2r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ch /\ ( ph /\ ps ) /\ th ) /\ ta ) -> ps )

  proof
    wch
    wph
    wps
    wa
    wth
    w3a
    wps
    wta
    wch
    wph
    wps
    wth
    simp2r
    adantr
end
