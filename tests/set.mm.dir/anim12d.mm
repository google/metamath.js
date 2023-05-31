include "wa.mm"
include "idd.mm"
include "syl2and.mm"

theorem anim12d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume anim12d.1: |- ( ph -> ( ps -> ch ) )
  assume anim12d.2: |- ( ph -> ( th -> ta ) )


  assert |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wch
    wta
    wa
    #
    anim12d.1
    anim12d.2
    wph
    @0
    idd
    syl2and
end
