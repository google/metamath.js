include "ancomsd.mm"
include "syland.mm"

theorem sylan2d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume sylan2d.1: |- ( ph -> ( ps -> ch ) )
  assume sylan2d.2: |- ( ph -> ( ( th /\ ch ) -> ta ) )


  assert |- ( ph -> ( ( th /\ ps ) -> ta ) )

  proof
    wph
    wps
    wth
    wta
    wph
    wps
    wch
    wth
    wta
    sylan2d.1
    wph
    wth
    wch
    wta
    sylan2d.2
    ancomsd
    syland
    ancomsd
end
