include "wa.mm"
include "expcom.mm"
include "adantrd.mm"
include "mpcom.mm"

theorem syldan
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume syldan.1: |- ( ( ph /\ ps ) -> ch )
  assume syldan.2: |- ( ( ph /\ ch ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wch
    wph
    wps
    wa
    wth
    syldan.1
    wch
    wph
    wth
    wps
    wph
    wch
    wth
    syldan.2
    expcom
    adantrd
    mpcom
end
