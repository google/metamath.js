include "w3a.mm"
include "simp3.mm"
include "adantr.mm"

theorem simpl3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wch
    wth
    wph
    wps
    wch
    simp3
    adantr
end
