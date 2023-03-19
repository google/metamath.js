include "wa.mm"
include "an32.mm"
include "sylbi.mm"

theorem an32s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume an32s.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ph /\ ch ) /\ ps ) -> th )

  proof
    wph
    wch
    wa
    wps
    wa
    wph
    wps
    wa
    wch
    wa
    wth
    wph
    wch
    wps
    an32
    an32s.1
    sylbi
end
