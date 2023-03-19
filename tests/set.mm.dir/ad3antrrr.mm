include "wa.mm"
include "adantr.mm"
include "ad2antrr.mm"

theorem ad3antrrr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) -> ps )

  proof
    wph
    wch
    wa
    wps
    wth
    wta
    wph
    wps
    wch
    ad2ant.1
    adantr
    ad2antrr
end
