include "adantr.mm"
include "adantlr.mm"

theorem ad2antrr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ph /\ ch ) /\ th ) -> ps )

  proof
    wph
    wth
    wps
    wch
    wph
    wps
    wth
    ad2ant.1
    adantr
    adantlr
end
