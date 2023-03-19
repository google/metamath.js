include "wa.mm"
include "w3a.mm"
include "simp1r.mm"
include "adantr.mm"

theorem simpl1r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ph /\ ps ) /\ ch /\ th ) /\ ta ) -> ps )

  proof
    wph
    wps
    wa
    wch
    wth
    w3a
    wps
    wta
    wph
    wps
    wch
    wth
    simp1r
    adantr
end
