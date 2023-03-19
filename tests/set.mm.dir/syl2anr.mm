include "syl2an.mm"
include "ancoms.mm"

theorem syl2anr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl2an.1: |- ( ph -> ps )
  assume syl2an.2: |- ( ta -> ch )
  assume syl2an.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ta /\ ph ) -> th )

  proof
    wph
    wta
    wth
    wph
    wps
    wch
    wth
    wta
    syl2an.1
    syl2an.2
    syl2an.3
    syl2an
    ancoms
end
