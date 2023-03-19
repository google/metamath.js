include "w3a.mm"
include "3simpa.mm"
include "simprd.mm"

theorem simp2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) -> ps )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wph
    wps
    wch
    3simpa
    simprd
end
