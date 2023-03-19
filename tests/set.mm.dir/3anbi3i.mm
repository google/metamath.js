include "biid.mm"
include "3anbi123i.mm"

theorem 3anbi3i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3anbi1i.1: |- ( ph <-> ps )


  assert |- ( ( ch /\ th /\ ph ) <-> ( ch /\ th /\ ps ) )

  proof
    wch
    wch
    wth
    wth
    wph
    wps
    wch
    biid
    wth
    biid
    3anbi1i.1
    3anbi123i
end
