include "wnf.mm"
include "wal.mm"
include "weq.mm"
include "wn.mm"
include "wsb.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "sbequ12.mm"
include "sps.mm"
include "drnf2.mm"
include "biimpd.mm"
include "spsd.mm"
include "impcom.mm"
include "a1d.mm"
include "nfnf1.mm"
include "nfal.mm"
include "nfnae.mm"
include "nfan.mm"
include "nfa1.mm"
include "sp.mm"
include "adantr.mm"
include "nfsb2.mm"
include "adantl.mm"
include "a1i.mm"
include "dvelimdf.mm"
include "pm2.61dan.mm"

theorem nfsb4t
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x F/ z ph -> ( -. A. z z = y -> F/ z [ y / x ] ph ) )

  proof
    wph
    vz
    wnf
    #
    vx
    wal
    #
    vx
    vy
    weq
    #
    vx
    wal
    #
    vz
    vy
    weq
    vz
    wal
    wn
    #
    wph
    vx
    vy
    wsb
    #
    vz
    wnf
    #
    wi
    @1
    @3
    wa
    @6
    @4
    @3
    @1
    @6
    @3
    @0
    @6
    vx
    @3
    @0
    @6
    wph
    @5
    vx
    vy
    vz
    @2
    wph
    @5
    wb
    #
    vx
    wph
    vx
    vy
    sbequ12
    #
    sps
    drnf2
    biimpd
    spsd
    impcom
    a1d
    @1
    @3
    wn
    #
    wa
    #
    wph
    @5
    vz
    vy
    vx
    @1
    @9
    vz
    @0
    vz
    vx
    wph
    vz
    nfnf1
    nfal
    vx
    vy
    vz
    nfnae
    nfan
    @1
    @9
    vx
    @0
    vx
    nfa1
    vx
    vy
    vx
    nfnae
    nfan
    @1
    @0
    @9
    @0
    vx
    sp
    adantr
    @9
    @5
    vx
    wnf
    @1
    wph
    vx
    vy
    nfsb2
    adantl
    @2
    @7
    wi
    @10
    @8
    a1i
    dvelimdf
    pm2.61dan
end
