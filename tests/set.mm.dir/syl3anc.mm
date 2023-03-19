include "w3a.mm"
include "3jca.mm"
include "syl.mm"

theorem syl3anc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume syl12anc.1: |- ( ph -> ps )
  assume syl12anc.2: |- ( ph -> ch )
  assume syl12anc.3: |- ( ph -> th )
  assume syl3anc.4: |- ( ( ps /\ ch /\ th ) -> ta )


  assert |- ( ph -> ta )

  proof
    wph
    wps
    wch
    wth
    w3a
    wta
    wph
    wps
    wch
    wth
    syl12anc.1
    syl12anc.2
    syl12anc.3
    3jca
    syl3anc.4
    syl
end
