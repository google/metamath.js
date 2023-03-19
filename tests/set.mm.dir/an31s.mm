include "exp31.mm"
include "com13.mm"
include "imp31.mm"

theorem an31s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume an32s.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ch /\ ps ) /\ ph ) -> th )

  proof
    wch
    wps
    wph
    wth
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    an32s.1
    exp31
    com13
    imp31
end
