include "weq.mm"
include "wal.mm"
include "wnf.mm"
include "wsb.mm"
include "wi.mm"
include "wb.mm"
include "sbequ12r.mm"
include "equcoms.mm"
include "sps.mm"
include "drnf1.mm"
include "biimprd.mm"
include "wn.mm"
include "nfsb2.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem wl-nfs1t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( F/ y ph -> F/ x [ y / x ] ph )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    #
    wph
    vy
    wnf
    #
    wph
    vx
    vy
    wsb
    #
    vx
    wnf
    #
    wi
    @1
    @4
    @2
    @3
    wph
    vx
    vy
    @0
    @3
    wph
    wb
    #
    vx
    @5
    vy
    vx
    wph
    vy
    vx
    sbequ12r
    equcoms
    sps
    drnf1
    biimprd
    @1
    wn
    @4
    @2
    wph
    vx
    vy
    nfsb2
    a1d
    pm2.61i
end
