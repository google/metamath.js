include "wa.mm"
include "adantrl.mm"
include "adantll.mm"

theorem ad2ant2l
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad2ant2.1: |- ( ( ph /\ ps ) -> ch )


  assert |- ( ( ( th /\ ph ) /\ ( ta /\ ps ) ) -> ch )

  proof
    wph
    wta
    wps
    wa
    wch
    wth
    wph
    wps
    wch
    wta
    ad2ant2.1
    adantrl
    adantll
end
