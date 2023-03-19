include "wa.mm"
include "ad3antrrr.mm"
include "adantr.mm"

theorem ad4antr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ( ( ph /\ ch ) /\ th ) /\ ta ) /\ et ) -> ps )

  proof
    wph
    wch
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
    ad3antrrr
    adantr
end
