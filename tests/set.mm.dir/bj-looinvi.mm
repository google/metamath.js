include "wi.mm"
include "looinv.mm"
include "ax-mp.mm"

theorem bj-looinvi
  let wph: wff ph
  let wps: wff ps
  assume bj-looinvi.1: |- ( ( ph -> ps ) -> ps )


  assert |- ( ( ps -> ph ) -> ph )

  proof
    wph
    wps
    wi
    wps
    wi
    wps
    wph
    wi
    wph
    wi
    bj-looinvi.1
    wph
    wps
    looinv
    ax-mp
end
