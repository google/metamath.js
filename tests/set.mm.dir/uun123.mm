include "w3a.mm"
include "3ancomb.mm"
include "sylbir.mm"

theorem uun123
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume uun123.1: |- ( ( ph /\ ch /\ ps ) -> th )


  assert |- ( ( ph /\ ps /\ ch ) -> th )

  proof
    wph
    wps
    wch
    w3a
    wph
    wch
    wps
    w3a
    wth
    wph
    wch
    wps
    3ancomb
    uun123.1
    sylbir
end
