include "wa.mm"
include "anbi2i.mm"
include "biancom.mm"

theorem anbi1ci
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anbi1ci.1: |- ( ph <-> ps )


  assert |- ( ( ch /\ ph ) <-> ( ps /\ ch ) )

  proof
    wch
    wph
    wa
    wps
    wch
    wph
    wps
    wch
    anbi1ci.1
    anbi2i
    biancom
end
