include "anassrs.mm"
include "anabss4.mm"

theorem anabss7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anabss7.1: |- ( ( ps /\ ( ph /\ ps ) ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wps
    wph
    wps
    wch
    anabss7.1
    anassrs
    anabss4
end
