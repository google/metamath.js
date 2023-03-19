include "wo.mm"
include "wn.mm"
include "wi.mm"
include "df-or.mm"
include "nfn.mm"
include "nfim.mm"
include "nfxfr.mm"

theorem nfor
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  assume nf.1: |- F/ x ph
  assume nf.2: |- F/ x ps


  assert |- F/ x ( ph \/ ps )

  proof
    wph
    wps
    wo
    wph
    wn
    #
    wps
    wi
    vx
    wph
    wps
    df-or
    @0
    wps
    vx
    wph
    vx
    nf.1
    nfn
    nf.2
    nfim
    nfxfr
end
