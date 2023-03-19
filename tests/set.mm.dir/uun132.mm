include "w3a.mm"
include "wa.mm"
include "3anass.mm"
include "sylbi.mm"

theorem uun132
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun132.1: |- ( ( ph /\ ( ps /\ ch ) ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wch
    wa
    wa
    wth
    wph
    wps
    wch
    3anass
    uun132.1
    sylbi
end
