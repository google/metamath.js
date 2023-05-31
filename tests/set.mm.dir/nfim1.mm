include "wal.mm"
include "wn.mm"
include "wo.mm"
include "wi.mm"
include "wnf.mm"
include "nf3.mm"
include "mpbi.mm"
include "nftht.mm"
include "sps.mm"
include "nfimd.mm"
include "pm2.21.mm"
include "alimi.mm"
include "syl.mm"
include "jaoi.mm"
include "ax-mp.mm"

theorem nfim1
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  assume nfim1.1: |- F/ x ph
  assume nfim1.2: |- ( ph -> F/ x ps )


  assert |- F/ x ( ph -> ps )

  proof
    wph
    vx
    wal
    #
    wph
    wn
    #
    vx
    wal
    #
    wo
    #
    wph
    wps
    wi
    #
    vx
    wnf
    #
    wph
    vx
    wnf
    @3
    nfim1.1
    wph
    vx
    nf3
    mpbi
    @0
    @5
    @2
    @0
    wph
    wps
    vx
    wph
    vx
    nftht
    wph
    wps
    vx
    wnf
    vx
    nfim1.2
    sps
    nfimd
    @2
    @4
    vx
    wal
    @5
    @1
    @4
    vx
    wph
    wps
    pm2.21
    alimi
    @4
    vx
    nftht
    syl
    jaoi
    ax-mp
end
