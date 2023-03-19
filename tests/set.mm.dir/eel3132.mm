include "wa.mm"
include "syl2an.mm"
include "3impdir.mm"

theorem eel3132
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eel3132.1: |- ( ( ph /\ ps ) -> ch )
  assume eel3132.2: |- ( ( th /\ ps ) -> ta )
  assume eel3132.3: |- ( ( ch /\ ta ) -> et )


  assert |- ( ( ph /\ th /\ ps ) -> et )

  proof
    wph
    wps
    wth
    wet
    wph
    wps
    wa
    wch
    wta
    wet
    wth
    wps
    wa
    eel3132.1
    eel3132.2
    eel3132.3
    syl2an
    3impdir
end
