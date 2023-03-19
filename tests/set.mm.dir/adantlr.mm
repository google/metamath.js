include "wa.mm"
include "simpl.mm"
include "sylan.mm"

theorem adantlr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume adant2.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ph /\ th ) /\ ps ) -> ch )

  proof
    wph
    wth
    wa
    wph
    wps
    wch
    wph
    wth
    simpl
    adant2.1
    sylan
end
