include "sylan2d.mm"
include "syland.mm"

theorem syl2and
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  param wet: wff et
  assume syl2and.1: |- ( ph -> ( ps -> ch ) )
  assume syl2and.2: |- ( ph -> ( th -> ta ) )
  assume syl2and.3: |- ( ph -> ( ( ch /\ ta ) -> et ) )


  assert |- ( ph -> ( ( ps /\ th ) -> et ) )

  proof
    wph
    wps
    wch
    wth
    wet
    syl2and.1
    wph
    wth
    wta
    wch
    wet
    syl2and.2
    syl2and.3
    sylan2d
    syland
end
