include "weq.mm"
include "wal.mm"
include "wsb.mm"
include "wb.mm"
include "sbequ12a.mm"
include "equcoms.mm"
include "sps.mm"
include "dral1.mm"
include "wn.mm"
include "nfnae.mm"
include "wnf.mm"
include "nfsb2.mm"
include "naecoms.mm"
include "wi.mm"
include "a1i.mm"
include "cbv2.mm"
include "pm2.61i.mm"

theorem sb9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x [ x / y ] ph <-> A. y [ y / x ] ph )

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
    vx
    wsb
    #
    vx
    wal
    wph
    vx
    vy
    wsb
    #
    vy
    wal
    wb
    @2
    @3
    vx
    vy
    @0
    @2
    @3
    wb
    #
    vx
    @4
    vy
    vx
    wph
    vy
    vx
    sbequ12a
    equcoms
    #
    sps
    dral1
    @1
    wn
    #
    @2
    @3
    vx
    vy
    vx
    vy
    vx
    nfnae
    vx
    vy
    vy
    nfnae
    @2
    vy
    wnf
    vy
    vx
    wph
    vy
    vx
    nfsb2
    naecoms
    wph
    vx
    vy
    nfsb2
    @0
    @4
    wi
    @6
    @5
    a1i
    cbv2
    pm2.61i
end
