include "exp32.mm"
include "imp31.mm"

theorem anassrs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anassrs.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ( ph /\ ps ) /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    anassrs.1
    exp32
    imp31
end
