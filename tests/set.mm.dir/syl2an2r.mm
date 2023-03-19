include "sylan.mm"
include "syldan.mm"

theorem syl2an2r
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
    wth
    wta
    syl2an2r.2
    wph
    wps
    wth
    wta
    syl2an2r.1
    syl2an2r.3
    sylan
    syldan
end
