include "wa.mm"
include "imp.mm"
include "anabss5.mm"

theorem anabsi5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabsi5.1: |- ( ph -> ( ( ph /\ ps ) -> ch ) )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wph
    wps
    wa
    wch
    anabsi5.1
    imp
    anabss5
end
