include "wa.mm"
include "jca.mm"
include "syl311anc.mm"

theorem syl321anc
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
  assume syl321anc.7: |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et ) /\ ze ) -> si )


  assert |- ( ph -> si )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wa
    wze
    wsi
    syl12anc.1
    syl12anc.2
    syl12anc.3
    wph
    wta
    wet
    syl22anc.4
    syl23anc.5
    jca
    syl33anc.6
    syl321anc.7
    syl311anc
end
