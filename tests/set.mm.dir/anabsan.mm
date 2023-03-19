include "wa.mm"
include "pm4.24.mm"
include "sylanb.mm"

theorem anabsan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabsan.1: |- ( ( ( ph /\ ph ) /\ ps ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wph
    wph
    wa
    wps
    wch
    wph
    pm4.24
    anabsan.1
    sylanb
end
