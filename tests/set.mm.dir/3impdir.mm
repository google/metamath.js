include "anandirs.mm"
include "3impa.mm"

theorem 3impdir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3impdir.1: |- ( ( ( ph /\ ps ) /\ ( ch /\ ps ) ) -> th )


  assert |- ( ( ph /\ ch /\ ps ) -> th )

  proof
    wph
    wch
    wps
    wth
    wph
    wch
    wps
    wth
    3impdir.1
    anandirs
    3impa
end
