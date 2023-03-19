include "wa.mm"
include "simpr.mm"
include "syl2anc.mm"

theorem sylancom
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume sylancom.1: |- ( ( ph /\ ps ) -> ch )
  assume sylancom.2: |- ( ( ch /\ ps ) -> th )


  assert |- ( ( ph /\ ps ) -> th )

  proof
    wph
    wps
    wa
    wch
    wps
    wth
    sylancom.1
    wph
    wps
    simpr
    sylancom.2
    syl2anc
end
