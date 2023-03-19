include "wa.mm"
include "com12.mm"
include "anabsi7.mm"

theorem syldbl2
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  assume syldbl2.1: |- ( ( ph /\ ps ) -> ( ps -> th ) )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    wth
    wph
    wps
    wa
    wps
    wth
    syldbl2.1
    com12
    anabsi7
end
