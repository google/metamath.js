include "wa.mm"
include "wi.mm"
include "adantr.mm"
include "adantl.mm"
include "jcad.mm"

theorem anim12ii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume anim12ii.1: |- ( ph -> ( ps -> ch ) )
  assume anim12ii.2: |- ( th -> ( ps -> ta ) )


  assert |- ( ( ph /\ th ) -> ( ps -> ( ch /\ ta ) ) )

  proof
    wph
    wth
    wa
    wps
    wch
    wta
    wph
    wps
    wch
    wi
    wth
    anim12ii.1
    adantr
    wth
    wps
    wta
    wi
    wph
    anim12ii.2
    adantl
    jcad
end
