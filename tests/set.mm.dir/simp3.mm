include "w3a.mm"
include "3simpc.mm"
include "simprd.mm"

theorem simp3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ps /\ ch ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wps
    wch
    wph
    wps
    wch
    3simpc
    simprd
end
