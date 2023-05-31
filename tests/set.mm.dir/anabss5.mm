include "anassrs.mm"
include "anabsan.mm"

theorem anabss5
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume anabss5.1: |- ( ( ph /\ ( ph /\ ps ) ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wph
    wps
    wch
    anabss5.1
    anassrs
    anabsan
end
