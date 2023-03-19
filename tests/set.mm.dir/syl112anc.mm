include "wa.mm"
include "jca.mm"
include "syl3anc.mm"

theorem syl112anc
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
  assume syl112anc.5: |- ( ( ps /\ ch /\ ( th /\ ta ) ) -> et )


  assert |- ( ph -> et )

  proof
    wph
    wps
    wch
    wth
    wta
    wa
    wet
    syl12anc.1
    syl12anc.2
    wph
    wth
    wta
    syl12anc.3
    syl22anc.4
    jca
    syl112anc.5
    syl3anc
end
