include "wa.mm"
include "jca.mm"
include "syl113anc.mm"

theorem syl123anc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  assume syl12anc.1: |- ( ph -> ps )
  assume syl12anc.2: |- ( ph -> ch )
  assume syl12anc.3: |- ( ph -> th )
  assume syl22anc.4: |- ( ph -> ta )
  assume syl23anc.5: |- ( ph -> et )
  assume syl33anc.6: |- ( ph -> ze )
  assume syl123anc.7: |- ( ( ps /\ ( ch /\ th ) /\ ( ta /\ et /\ ze ) ) -> si )


  assert |- ( ph -> si )

  proof
    wph
    wps
    wch
    wth
    wa
    wta
    wet
    wze
    wsi
    syl12anc.1
    wph
    wch
    wth
    syl12anc.2
    syl12anc.3
    jca
    syl22anc.4
    syl23anc.5
    syl33anc.6
    syl123anc.7
    syl113anc
end
