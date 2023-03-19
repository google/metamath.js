include "w3a.mm"
include "wa.mm"
include "simpl2.mm"
include "adantr.mm"

theorem simpll2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ( ( ph /\ ps /\ ch ) /\ th ) /\ ta ) -> ps )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wps
    wta
    wph
    wps
    wch
    wth
    simpl2
    adantr
end
