include "wa.mm"
include "wi.mm"
include "ex.mm"
include "adantllr.mm"
include "imp.mm"

theorem adantl3r
  let wph: wff ph
  let wsi: wff si
  let wrh: wff rh
  let wmu: wff mu
  let wla: wff la
  let wka: wff ka
  assume adantl3r.1: |- ( ( ( ( ph /\ rh ) /\ mu ) /\ la ) -> ka )


  assert |- ( ( ( ( ( ph /\ si ) /\ rh ) /\ mu ) /\ la ) -> ka )

  proof
    wph
    wsi
    wa
    wrh
    wa
    wmu
    wa
    wla
    wka
    wph
    wrh
    wmu
    wla
    wka
    wi
    wsi
    wph
    wrh
    wa
    wmu
    wa
    wla
    wka
    adantl3r.1
    ex
    adantllr
    imp
end
