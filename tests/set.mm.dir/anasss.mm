include "exp31.mm"
include "imp32.mm"

theorem anasss
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anasss.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    anasss.1
    exp31
    imp32
end
