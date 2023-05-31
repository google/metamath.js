include "wa.mm"
include "ancom.mm"
include "syl5bi.mm"

theorem ancomsd
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume ancomsd.1: |- ( ph -> ( ( ps /\ ch ) -> th ) )


  assert |- ( ph -> ( ( ch /\ ps ) -> th ) )

  proof
    wch
    wps
    wa
    wps
    wch
    wa
    wph
    wth
    wch
    wps
    ancom
    ancomsd.1
    syl5bi
end
