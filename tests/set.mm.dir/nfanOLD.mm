include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-an.mm"
include "nfn.mm"
include "nfim.mm"
include "nfxfr.mm"

theorem nfanOLD
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfan.1: |- F/ x ph
  assume nfan.2: |- F/ x ps


  assert |- F/ x ( ph /\ ps )

  proof
    wph
    wps
    wa
    wph
    wps
    wn
    #
    wi
    #
    wn
    vx
    wph
    wps
    df-an
    @1
    vx
    wph
    @0
    vx
    nfan.1
    wps
    vx
    nfan.2
    nfn
    nfim
    nfn
    nfxfr
end
