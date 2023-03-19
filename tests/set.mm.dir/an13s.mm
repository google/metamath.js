include "exp32.mm"
include "com13.mm"
include "imp32.mm"

theorem an13s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume an12s.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ch /\ ( ps /\ ph ) ) -> th )

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
    an12s.1
    exp32
    com13
    imp32
end
