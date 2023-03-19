include "wa.mm"
include "syl2an.mm"
include "3impb.mm"

theorem eel132
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume eel132.1: |- ( ph -> ps )
  assume eel132.2: |- ( ( ch /\ th ) -> ta )
  assume eel132.3: |- ( ( ps /\ ta ) -> et )


  assert |- ( ( ph /\ ch /\ th ) -> et )

  proof
    wph
    wch
    wth
    wet
    wph
    wps
    wta
    wet
    wch
    wth
    wa
    eel132.1
    eel132.2
    eel132.3
    syl2an
    3impb
end
