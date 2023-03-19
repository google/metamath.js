include "wnan.mm"
include "wa.mm"
include "wn.mm"
include "df-nan.mm"
include "nfan.mm"
include "nfn.mm"
include "nfxfr.mm"

theorem nfnan
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfan.1: |- F/ x ph
  assume nfan.2: |- F/ x ps


  assert |- F/ x ( ph -/\ ps )

  proof
    wph
    wps
    wnan
    wph
    wps
    wa
    #
    wn
    vx
    wph
    wps
    df-nan
    @0
    vx
    wph
    wps
    vx
    nfan.1
    nfan.2
    nfan
    nfn
    nfxfr
end
