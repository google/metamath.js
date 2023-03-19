include "wa.mm"
include "wi.mm"
include "ex.mm"
include "adantl5r.mm"
include "imp.mm"

theorem adantl6r
  let wph: wff ph
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu
  let wla: wff la
  let wka: wff ka
  assume adantl6r.1: |- ( ( ( ( ( ( ( ph /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka )


  assert |- ( ( ( ( ( ( ( ( ph /\ ta ) /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka )

  proof
    wph
    wta
    wa
    wet
    wa
    wze
    wa
    wsi
    wa
    wrh
    wa
    wmu
    wa
    wla
    wka
    wph
    wta
    wet
    wze
    wsi
    wrh
    wmu
    wla
    wka
    wi
    wph
    wet
    wa
    wze
    wa
    wsi
    wa
    wrh
    wa
    wmu
    wa
    wla
    wka
    adantl6r.1
    ex
    adantl5r
    imp
end
