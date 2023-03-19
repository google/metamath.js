include "3com12.mm"

theorem uun123p1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun123p1.1: |- ( ( ps /\ ph /\ ch ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wps
    wph
    wch
    wth
    uun123p1.1
    3com12
end
