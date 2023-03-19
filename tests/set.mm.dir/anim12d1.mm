include "wi.mm"
include "a1i.mm"
include "anim12d.mm"

theorem anim12d1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume anim12d1.1: |- ( ph -> ( ps -> ch ) )
  assume anim12d1.2: |- ( th -> ta )


  assert |- ( ph -> ( ( ps /\ th ) -> ( ch /\ ta ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    anim12d1.1
    wth
    wta
    wi
    wph
    anim12d1.2
    a1i
    anim12d
end
