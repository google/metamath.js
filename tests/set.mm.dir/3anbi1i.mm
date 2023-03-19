include "biid.mm"
include "3anbi123i.mm"

theorem 3anbi1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3anbi1i.1: |- ( ph <-> ps )


  assert |- ( ( ph /\ ch /\ th ) <-> ( ps /\ ch /\ th ) )

  proof
    wph
    wps
    wch
    wch
    wth
    wth
    3anbi1i.1
    wch
    biid
    wth
    biid
    3anbi123i
end
