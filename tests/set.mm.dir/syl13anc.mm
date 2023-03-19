include "w3a.mm"
include "3jca.mm"
include "syl2anc.mm"

theorem syl13anc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume syl12anc.1: |- ( ph -> ps )
  assume syl12anc.2: |- ( ph -> ch )
  assume syl12anc.3: |- ( ph -> th )
  assume syl22anc.4: |- ( ph -> ta )
  assume syl13anc.5: |- ( ( ps /\ ( ch /\ th /\ ta ) ) -> et )


  assert |- ( ph -> et )

  proof
    wph
    wps
    wch
    wth
    wta
    w3a
    wet
    syl12anc.1
    wph
    wch
    wth
    wta
    syl12anc.2
    syl12anc.3
    syl22anc.4
    3jca
    syl13anc.5
    syl2anc
end
