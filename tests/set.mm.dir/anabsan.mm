include "wa.mm"
include "pm4.24.mm"
include "sylanb.mm"

theorem anabsan
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
