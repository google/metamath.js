include "wa.mm"
include "wi.mm"
include "ex.mm"
include "adantl3r.mm"
include "imp.mm"

theorem adantl4r
  let wph: wff ph
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu
  let wla: wff la
  let wka: wff ka
  assume adantl4r.1: |- ( ( ( ( ( ph /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka )


  assert |- ( ( ( ( ( ( ph /\ ze ) /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka )

  proof
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
    wph
    wze
    wsi
    wrh
    wmu
    wla
    wka
    wi
    wph
    wsi
    wa
    wrh
    wa
    wmu
    wa
    wla
    wka
    adantl4r.1
    ex
    adantl3r
    imp
end
