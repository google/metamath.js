include "w3o.mm"
include "wo.mm"
include "df-3or.mm"
include "nforOLD.mm"
include "nfxfrOLD.mm"

theorem nf3orOLD
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfOLD.1: |- nfOLD x ph
  assume nfOLD.2: |- nfOLD x ps
  assume nfOLD.3: |- nfOLD x ch


  assert |- nfOLD x ( ph \/ ps \/ ch )

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
    nfOLD.1
    nfOLD.2
    nforOLD
    nfOLD.3
    nforOLD
    nfxfrOLD
end
