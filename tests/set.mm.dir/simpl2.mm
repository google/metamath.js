include "w3a.mm"
include "simp2.mm"
include "adantr.mm"

theorem simpl2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph /\ ps /\ ch ) /\ th ) -> ps )

  proof
    wph
    wps
    wch
    w3a
    wps
    wth
    wph
    wps
    wch
    simp2
    adantr
end
