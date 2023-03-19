include "syldan.mm"

theorem stoic2a
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume stoic2a.1: |- ( ( ph /\ ps ) -> ch )
  assume stoic2a.2: |- ( ( ph /\ ch ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    wch
    wth
    stoic2a.1
    stoic2a.2
    syldan
end
