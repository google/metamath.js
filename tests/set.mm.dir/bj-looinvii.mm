include "wi.mm"
include "bj-looinvi.mm"
include "ax-mp.mm"

theorem bj-looinvii
  let wph: wff ph
  let wps: wff ps
  assume bj-looinvii.1: |- ( ( ph -> ps ) -> ps )
  assume bj-looinvii.2: |- ( ps -> ph )


  assert |- ph

  proof
    wps
    wph
    wi
    wph
    bj-looinvii.2
    wph
    wps
    bj-looinvii.1
    bj-looinvi
    ax-mp
end
