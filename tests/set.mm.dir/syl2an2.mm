include "wa.mm"
include "syl2an.mm"
include "anabss7.mm"

theorem syl2an2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl2an2.1: |- ( ph -> ps )
  assume syl2an2.2: |- ( ( ch /\ ph ) -> th )
  assume syl2an2.3: |- ( ( ps /\ th ) -> ta )


  assert |- ( ( ch /\ ph ) -> ta )

  proof
    wch
    wph
    wta
    wph
    wps
    wth
    wta
    wch
    wph
    wa
    syl2an2.1
    syl2an2.2
    syl2an2.3
    syl2an
    anabss7
end
