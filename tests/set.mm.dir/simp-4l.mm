include "wa.mm"
include "simplll.mm"
include "adantr.mm"

theorem simp-4l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ( ph /\ ps ) /\ ch ) /\ th ) /\ ta ) -> ph )

  proof
    wph
    wps
    wa
    wch
    wa
    wth
    wa
    wph
    wta
    wph
    wps
    wch
    wth
    simplll
    adantr
end
