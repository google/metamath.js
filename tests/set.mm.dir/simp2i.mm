include "w3a.mm"
include "simp2.mm"
include "ax-mp.mm"

theorem simp2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3simp1i.1: |- ( ph /\ ps /\ ch )


  assert |- ps

  proof
    wph
    wps
    wch
    w3a
    wps
    3simp1i.1
    wph
    wps
    wch
    simp2
    ax-mp
end
