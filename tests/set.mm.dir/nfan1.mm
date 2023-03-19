include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-an.mm"
include "wnf.mm"
include "nfnt.mm"
include "syl.mm"
include "nfim1.mm"
include "nfn.mm"
include "nfxfr.mm"

theorem nfan1
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nfim1.1: |- F/ x ph
  assume nfim1.2: |- ( ph -> F/ x ps )


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
    nfim1.1
    wph
    wps
    vx
    wnf
    @0
    vx
    wnf
    nfim1.2
    wps
    vx
    nfnt
    syl
    nfim1
    nfn
    nfxfr
end
