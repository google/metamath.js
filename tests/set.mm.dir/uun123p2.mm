include "3coml.mm"

theorem uun123p2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun123p2.1: |- ( ( ch /\ ph /\ ps ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wch
    wph
    wps
    wth
    uun123p2.1
    3coml
end
