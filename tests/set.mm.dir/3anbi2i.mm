include "biid.mm"
include "3anbi123i.mm"

theorem 3anbi2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3anbi1i.1: |- ( ph <-> ps )


  assert |- ( ( ch /\ ph /\ th ) <-> ( ch /\ ps /\ th ) )

  proof
    wch
    wch
    wph
    wps
    wth
    wth
    wch
    biid
    3anbi1i.1
    wth
    biid
    3anbi123i
end
