include "w3a.mm"
include "wa.mm"
include "simpl3.mm"
include "adantr.mm"

theorem simpll3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wch
    wta
    wph
    wps
    wch
    wth
    simpl3
    adantr
end
