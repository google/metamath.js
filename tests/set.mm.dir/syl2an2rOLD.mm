include "wa.mm"
include "syl2an.mm"
include "anabss5.mm"

theorem syl2an2rOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl2an2r.1: |- ( ph -> ps )
  assume syl2an2r.2: |- ( ( ph /\ ch ) -> th )
  assume syl2an2r.3: |- ( ( ps /\ th ) -> ta )


  assert |- ( ( ph /\ ch ) -> ta )

  proof
    wph
    wch
    wta
    wph
    wps
    wth
    wta
    wph
    wch
    wa
    syl2an2r.1
    syl2an2r.2
    syl2an2r.3
    syl2an
    anabss5
end
