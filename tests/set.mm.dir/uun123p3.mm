include "3comr.mm"

theorem uun123p3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun123p3.1: |- ( ( ps /\ ch /\ ph ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wps
    wch
    wph
    wth
    uun123p3.1
    3comr
end
