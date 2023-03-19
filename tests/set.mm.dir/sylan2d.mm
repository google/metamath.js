include "ancomsd.mm"
include "syland.mm"

theorem sylan2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
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
