include "wnf.mm"
include "wal.mm"
include "weq.mm"
include "wb.mm"
include "wex.mm"
include "wsb.mm"
include "weu.mm"
include "nfnf1.mm"
include "nfal.mm"
include "equsb3.mm"
include "sblbis.mm"
include "nfa1.mm"
include "sp.mm"
include "nfsbd.mm"
include "nfvd.mm"
include "nfbid.mm"
include "nfxfrd.mm"
include "wi.mm"
include "sbequ.mm"
include "a1i.mm"
include "cbvald.mm"
include "nfv.mm"
include "sb8.mm"
include "bicomi.mm"
include "albii.mm"
include "3bitr3g.mm"
include "exbidv.mm"
include "df-eu.mm"
include "3bitr4g.mm"

theorem wl-sb8eut
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v


  assert |- ( A. x F/ y ph -> ( E! x ph <-> E! y [ y / x ] ph ) )

  proof
    wph
    vy
    wnf
    #
    vx
    wal
    #
    wph
    vx
    vu
    weq
    #
    wb
    #
    vx
    wal
    #
    vu
    wex
    wph
    vx
    vy
    wsb
    #
    vy
    vu
    weq
    #
    wb
    #
    vy
    wal
    #
    vu
    wex
    wph
    vx
    weu
    @5
    vy
    weu
    @1
    @4
    @8
    vu
    @1
    @3
    vx
    vv
    wsb
    #
    vv
    wal
    #
    @3
    vx
    vy
    wsb
    #
    vy
    wal
    @4
    @8
    @1
    @9
    @11
    vv
    vy
    @0
    vy
    vx
    wph
    vy
    nfnf1
    nfal
    @9
    wph
    vx
    vv
    wsb
    #
    vv
    vu
    weq
    #
    wb
    @1
    vy
    @2
    @13
    wph
    vx
    vv
    vv
    vx
    vu
    equsb3
    sblbis
    @1
    @12
    @13
    vy
    @1
    wph
    vx
    vv
    vy
    @0
    vx
    nfa1
    @0
    vx
    sp
    nfsbd
    @1
    @13
    vy
    nfvd
    nfbid
    nfxfrd
    vv
    vy
    weq
    @9
    @11
    wb
    wi
    @1
    @3
    vv
    vy
    vx
    sbequ
    a1i
    cbvald
    @4
    @10
    @3
    vx
    vv
    @3
    vv
    nfv
    sb8
    bicomi
    @11
    @7
    vy
    @2
    @6
    wph
    vx
    vy
    vy
    vx
    vu
    equsb3
    sblbis
    albii
    3bitr3g
    exbidv
    wph
    vx
    vu
    df-eu
    @5
    vy
    vu
    df-eu
    3bitr4g
end
