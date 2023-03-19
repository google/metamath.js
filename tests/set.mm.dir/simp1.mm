include "w3a.mm"
include "3simpa.mm"
include "simpld.mm"

theorem simp1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) -> ph )

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
    simpld
end
