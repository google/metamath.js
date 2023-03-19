include "wa.mm"
include "id.mm"
include "syl2an.mm"

theorem anim12i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anim12i.1: |- ( ph -> ps )
  assume anim12i.2: |- ( ch -> th )


  assert |- ( ( ph /\ ch ) -> ( ps /\ th ) )

  proof
    wph
    wps
    wth
    wps
    wth
    wa
    #
    wch
    anim12i.1
    anim12i.2
    @0
    id
    syl2an
end
