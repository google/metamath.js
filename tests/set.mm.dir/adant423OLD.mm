include "wa.mm"
include "simplll.mm"
include "sylancom.mm"

theorem adant423OLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume adant423.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( ( ph /\ th ) /\ ta ) /\ ps ) -> ch )

  proof
    wph
    wth
    wa
    wta
    wa
    wps
    wph
    wch
    wph
    wth
    wta
    wps
    simplll
    adant423.1
    sylancom
end
