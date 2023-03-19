include "wa.mm"
include "simp-5l.mm"
include "adantr.mm"

theorem simp-6l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze


  assert |- ( ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) /\ ze ) -> ph )

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
    wph
    wze
    wph
    wps
    wch
    wth
    wta
    wet
    simp-5l
    adantr
end
