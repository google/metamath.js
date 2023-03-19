include "wa.mm"
include "simp-5r.mm"
include "adantr.mm"

theorem simp-6r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ps )

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
    wet
    wa
    wps
    wze
    wph
    wps
    wch
    wth
    wta
    wet
    simp-5r
    adantr
end
