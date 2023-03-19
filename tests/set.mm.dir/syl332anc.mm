include "wa.mm"
include "jca.mm"
include "syl331anc.mm"

theorem syl332anc
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu
  assume syl12anc.1: |- ( ph -> ps )
  assume syl12anc.2: |- ( ph -> ch )
  assume syl12anc.3: |- ( ph -> th )
  assume syl22anc.4: |- ( ph -> ta )
  assume syl23anc.5: |- ( ph -> et )
  assume syl33anc.6: |- ( ph -> ze )
  assume syl133anc.7: |- ( ph -> si )
  assume syl233anc.8: |- ( ph -> rh )
  assume syl332anc.9: |- ( ( ( ps /\ ch /\ th ) /\ ( ta /\ et /\ ze ) /\ ( si /\ rh ) ) -> mu )


  assert |- ( ph -> mu )

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    wze
    wsi
    wrh
    wa
    wmu
    syl12anc.1
    syl12anc.2
    syl12anc.3
    syl22anc.4
    syl23anc.5
    syl33anc.6
    wph
    wsi
    wrh
    syl133anc.7
    syl233anc.8
    jca
    syl332anc.9
    syl331anc
end
