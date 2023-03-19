include "w3a.mm"
include "wa.mm"
include "simpl1.mm"
include "adantr.mm"

theorem simpll1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ph )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wph
    wta
    wph
    wps
    wch
    wth
    simpl1
    adantr
end
