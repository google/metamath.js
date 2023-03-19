include "w3a.mm"
include "wa.mm"
include "df-3an.mm"
include "nfan.mm"
include "nfxfr.mm"

theorem nf3an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  assume nfan.1: |- F/ x ph
  assume nfan.2: |- F/ x ps
  assume nfan.3: |- F/ x ch


  assert |- F/ x ( ph /\ ps /\ ch )

  proof
    wph
    wps
    wch
    w3a
    wph
    wps
    wa
    #
    wch
    wa
    vx
    wph
    wps
    wch
    df-3an
    @0
    wch
    vx
    wph
    wps
    vx
    nfan.1
    nfan.2
    nfan
    nfan.3
    nfan
    nfxfr
end
