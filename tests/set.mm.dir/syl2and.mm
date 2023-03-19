include "sylan2d.mm"
include "syland.mm"

theorem syl2and
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
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
