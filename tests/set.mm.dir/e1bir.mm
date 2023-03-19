include "biimpri.mm"
include "e1a.mm"

theorem e1bir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume e1bir.1: |- (. ph ->. ps ).
  assume e1bir.2: |- ( ch <-> ps )


  assert |- (. ph ->. ch ).

  proof
    wph
    wps
    wch
    e1bir.1
    wch
    wps
    e1bir.2
    biimpri
    e1a
end
