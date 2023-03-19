include "w3a.mm"
include "simp3.mm"
include "ax-mp.mm"

theorem simp3i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3simp1i.1: |- ( ph /\ ps /\ ch )


  assert |- ch

  proof
    wph
    wps
    wch
    w3a
    wch
    3simp1i.1
    wph
    wps
    wch
    simp3
    ax-mp
end
