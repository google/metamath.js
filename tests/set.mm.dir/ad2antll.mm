include "wa.mm"
include "adantl.mm"

theorem ad2antll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ad2ant.1: |- ( ph -> ps )


  assert |- ( ( ch /\ ( th /\ ph ) ) -> ps )

  proof
    wth
    wph
    wa
    wps
    wch
    wph
    wps
    wth
    ad2ant.1
    adantl
    adantl
end
