include "wa.mm"
include "simp-4r.mm"
include "adantr.mm"

theorem simp-5r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) -> ps )

  proof
    wph
    wps
    wa
    wch
    wa
    wth
    wa
    wta
    wa
    wps
    wet
    wph
    wps
    wch
    wth
    wta
    simp-4r
    adantr
end
