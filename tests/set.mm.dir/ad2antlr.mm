include "adantr.mm"
include "adantll.mm"

theorem ad2antlr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ( ch /\ ph ) /\ th ) -> ps )

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
    adantll
end
