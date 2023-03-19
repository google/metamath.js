include "wa.mm"
include "simp-4l.mm"
include "adantr.mm"

theorem simp-5l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) /\ et ) -> ph )

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
    wph
    wet
    wph
    wps
    wch
    wth
    wta
    simp-4l
    adantr
end
