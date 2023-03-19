include "anassrs.mm"
include "an32s.mm"

theorem anass1rs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anass1rs.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ( ph /\ ch ) /\ ps ) -> th )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    anass1rs.1
    anassrs
    an32s
end
