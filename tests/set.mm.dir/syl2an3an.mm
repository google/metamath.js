include "syl3an.mm"
include "3anidm12.mm"

theorem syl2an3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl2an3an.1: |- ( ph -> ps )
  assume syl2an3an.2: |- ( ph -> ch )
  assume syl2an3an.3: |- ( th -> ta )
  assume syl2an3an.4: |- ( ( ps /\ ch /\ ta ) -> et )


  assert |- ( ( ph /\ th ) -> et )

  proof
    wph
    wth
    wet
    wph
    wps
    wph
    wch
    wth
    wta
    wet
    syl2an3an.1
    syl2an3an.2
    syl2an3an.3
    syl2an3an.4
    syl3an
    3anidm12
end
