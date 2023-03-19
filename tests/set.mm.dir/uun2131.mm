include "3impdi.mm"

theorem uun2131
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun2131.1: |- ( ( ( ph /\ ps ) /\ ( ph /\ ch ) ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    wth
    uun2131.1
    3impdi
end
