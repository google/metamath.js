include "wa.mm"
include "ad2antlr.mm"
include "adantr.mm"

theorem ad3antlr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) -> ps )

  proof
    wch
    wph
    wa
    wth
    wa
    wps
    wta
    wph
    wps
    wch
    wth
    ad2ant.1
    ad2antlr
    adantr
end
