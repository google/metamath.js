include "wa.mm"
include "anbi1i.mm"
include "ancom.mm"
include "bitri.mm"

theorem anbi2ci
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anbi.1: |- ( ph <-> ps )


  assert |- ( ( ph /\ ch ) <-> ( ch /\ ps ) )

  proof
    wph
    wch
    wa
    wps
    wch
    wa
    wch
    wps
    wa
    wph
    wps
    wch
    anbi.1
    anbi1i
    wps
    wch
    ancom
    bitri
end
