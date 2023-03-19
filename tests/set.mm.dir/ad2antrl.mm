include "wa.mm"
include "adantr.mm"
include "adantl.mm"

theorem ad2antrl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ch /\ ( ph /\ th ) ) -> ps )

  proof
    wph
    wth
    wa
    wps
    wch
    wph
    wps
    wth
    ad2ant.1
    adantr
    adantl
end
