include "wa.mm"
include "uunT1.mm"

theorem uunT21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume uunT21.1: |- ( ( T. /\ ( ph /\ ps ) ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wa
    wch
    uunT21.1
    uunT1
end
