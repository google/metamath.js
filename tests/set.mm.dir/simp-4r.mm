include "wa.mm"
include "simpllr.mm"
include "adantr.mm"

theorem simp-4r
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ps )

  proof
    wph
    wps
    wa
    wch
    wa
    wth
    wa
    wps
    wta
    wph
    wps
    wch
    wth
    simpllr
    adantr
end
