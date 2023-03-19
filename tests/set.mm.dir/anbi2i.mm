include "wb.mm"
include "a1i.mm"
include "pm5.32i.mm"

theorem anbi2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anbi.1: |- ( ph <-> ps )


  assert |- ( ( ch /\ ph ) <-> ( ch /\ ps ) )

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
    pm5.32i
end
