include "wa.mm"
include "ad3antlr.mm"
include "adantr.mm"

theorem ad4antlr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ch /\ ph ) /\ th ) /\ ta ) /\ et ) -> ps )

  proof
    wch
    wph
    wa
    wth
    wa
    wta
    wa
    wps
    wet
    wph
    wps
    wch
    wth
    wta
    ad2ant.1
    ad3antlr
    adantr
end
