include "wa.mm"
include "pm3.22.mm"
include "sylan.mm"

theorem ancom1s
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume an32s.1: |- ( ( ( ph /\ ps ) /\ ch ) -> th )


  assert |- ( ( ( ps /\ ph ) /\ ch ) -> th )

  proof
    wps
    wph
    wa
    wph
    wps
    wa
    wch
    wth
    wps
    wph
    pm3.22
    an32s.1
    sylan
end
