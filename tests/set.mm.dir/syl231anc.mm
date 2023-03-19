include "wa.mm"
include "jca.mm"
include "syl131anc.mm"

theorem syl231anc
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
  assume syl231anc.7: |- ( ( ( ps /\ ch ) /\ ( th /\ ta /\ et ) /\ ze ) -> si )


  assert |- ( ph -> si )

  proof
    wph
    wps
    wch
    wa
    wth
    wta
    wet
    wze
    wsi
    wph
    wps
    wch
    syl12anc.1
    syl12anc.2
    jca
    syl12anc.3
    syl22anc.4
    syl23anc.5
    syl33anc.6
    syl231anc.7
    syl131anc
end
