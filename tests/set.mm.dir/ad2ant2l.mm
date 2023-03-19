include "wa.mm"
include "adantrl.mm"
include "adantll.mm"

theorem ad2ant2l
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
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
