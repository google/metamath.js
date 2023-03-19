include "3com13.mm"

theorem uun123p4
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun123p4.1: |- ( ( ch /\ ps /\ ph ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wch
    wps
    wph
    wth
    uun123p4.1
    3com13
end
