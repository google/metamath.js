include "wa.mm"
include "anbi12i.mm"
include "ancom.mm"
include "bitri.mm"

theorem anbi12ci
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anbi12.1: |- ( ph <-> ps )
  assume anbi12.2: |- ( ch <-> th )


  assert |- ( ( ph /\ ch ) <-> ( th /\ ps ) )

  proof
    wph
    wch
    wa
    wps
    wth
    wa
    wth
    wps
    wa
    wph
    wps
    wch
    wth
    anbi12.1
    anbi12.2
    anbi12i
    wps
    wth
    ancom
    bitri
end
