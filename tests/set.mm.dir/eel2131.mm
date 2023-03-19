include "wa.mm"
include "syl2an.mm"
include "3impdi.mm"

theorem eel2131
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eel2131.1: |- ( ( ph /\ ps ) -> ch )
  assume eel2131.2: |- ( ( ph /\ th ) -> ta )
  assume eel2131.3: |- ( ( ch /\ ta ) -> et )


  assert |- ( ( ph /\ ps /\ th ) -> et )

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
    wph
    wth
    wa
    eel2131.1
    eel2131.2
    eel2131.3
    syl2an
    3impdi
end
