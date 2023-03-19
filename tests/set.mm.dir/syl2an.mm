include "sylan.mm"
include "sylan2.mm"

theorem syl2an
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
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
