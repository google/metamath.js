include "w3o.mm"
include "wo.mm"
include "df-3or.mm"
include "nfor.mm"
include "nfxfr.mm"

theorem nf3or
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nf.1: |- F/ x ph
  assume nf.2: |- F/ x ps
  assume nf.3: |- F/ x ch


  assert |- F/ x ( ph \/ ps \/ ch )

  proof
    wph
    wps
    wch
    w3o
    wph
    wps
    wo
    #
    wch
    wo
    vx
    wph
    wps
    wch
    df-3or
    @0
    wch
    vx
    wph
    wps
    vx
    nf.1
    nf.2
    nfor
    nf.3
    nfor
    nfxfr
end
