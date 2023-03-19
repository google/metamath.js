include "w3a.mm"
include "simp1.mm"
include "adantr.mm"

theorem simpl1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ph )

  proof
    wph
    wps
    wch
    w3a
    wph
    wth
    wph
    wps
    wch
    simp1
    adantr
end
