include "sylan.mm"
include "sylan2.mm"

theorem syl2an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl2an.1: |- ( ph -> ps )
  assume syl2an.2: |- ( ta -> ch )
  assume syl2an.3: |- ( ( ps /\ ch ) -> th )


  assert |- ( ( ph /\ ta ) -> th )

  proof
    wta
    wph
    wch
    wth
    syl2an.2
    wph
    wps
    wch
    wth
    syl2an.1
    syl2an.3
    sylan
    sylan2
end
