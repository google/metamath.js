include "wb.mm"
include "a1i.mm"
include "pm5.32ri.mm"

theorem anbi1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anbi.1: |- ( ph <-> ps )


  assert |- ( ( ph /\ ch ) <-> ( ps /\ ch ) )

  proof
    wch
    wph
    wps
    wph
    wps
    wb
    wch
    anbi.1
    a1i
    pm5.32ri
end
