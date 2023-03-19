include "w3a.mm"
include "simp1.mm"
include "ax-mp.mm"

theorem simp1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3simp1i.1: |- ( ph /\ ps /\ ch )


  assert |- ph

  proof
    wph
    wps
    wch
    w3a
    wph
    3simp1i.1
    wph
    wps
    wch
    simp1
    ax-mp
end
