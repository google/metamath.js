include "wa.mm"
include "pm3.22.mm"
include "sylan2.mm"

theorem ancom2s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume an12s.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ( ch /\ ps ) ) -> th )

  proof
    wch
    wps
    wa
    wph
    wps
    wch
    wa
    wth
    wch
    wps
    pm3.22
    an12s.1
    sylan2
end
