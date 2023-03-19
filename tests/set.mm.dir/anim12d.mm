include "wa.mm"
include "idd.mm"
include "syl2and.mm"

theorem anim12d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
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
