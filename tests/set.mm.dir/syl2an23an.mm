include "wa.mm"
include "wi.mm"
include "3exp.mm"
include "sylc.mm"
include "syl5.mm"
include "anabsi7.mm"

theorem syl2an23an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl2an23an.1: |- ( ph -> ps )
  assume syl2an23an.2: |- ( ph -> ch )
  assume syl2an23an.3: |- ( ( th /\ ph ) -> ta )
  assume syl2an23an.4: |- ( ( ps /\ ch /\ ta ) -> et )


  assert |- ( ( th /\ ph ) -> et )

  proof
    wth
    wph
    wet
    wth
    wph
    wa
    wta
    wph
    wet
    syl2an23an.3
    wph
    wps
    wch
    wta
    wet
    wi
    syl2an23an.1
    syl2an23an.2
    wps
    wch
    wta
    wet
    syl2an23an.4
    3exp
    sylc
    syl5
    anabsi7
end
