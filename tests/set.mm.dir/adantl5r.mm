include "wa.mm"
include "wi.mm"
include "ex.mm"
include "adantl4r.mm"
include "imp.mm"

theorem adantl5r
  let wph: wff ph
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu
  let wla: wff la
  let wka: wff ka
  assume adantl5r.1: |- ( ( ( ( ( ( ph /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka )


  assert |- ( ( ( ( ( ( ( ph /\ et ) /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka )

  proof
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
    wph
    wet
    wze
    wsi
    wrh
    wmu
    wla
    wka
    wi
    wph
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
    adantl5r.1
    ex
    adantl4r
    imp
end
