include "wsb.mm"
include "weq.mm"
include "wal.mm"
include "wb.mm"
include "nfa1.mm"
include "sbequ.mm"
include "sps.mm"
include "sbbid.mm"
include "wn.mm"
include "wi.mm"
include "pm5.74i.mm"
include "albii.mm"
include "a1i.mm"
include "sb4b.mm"
include "3bitr4d.mm"
include "pm2.61i.mm"
include "sbcom.mm"
include "bitri.mm"

theorem wl-sbcom3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( [ z / y ] [ y / x ] ph <-> [ z / x ] [ z / y ] ph )

  proof
    wph
    vx
    vy
    wsb
    #
    vy
    vz
    wsb
    #
    wph
    vx
    vz
    wsb
    #
    vy
    vz
    wsb
    #
    wph
    vy
    vz
    wsb
    vx
    vz
    wsb
    vy
    vz
    weq
    #
    vy
    wal
    #
    @1
    @3
    wb
    @5
    @0
    @2
    vy
    vz
    @4
    vy
    nfa1
    @4
    @0
    @2
    wb
    vy
    wph
    vy
    vz
    vx
    sbequ
    #
    sps
    sbbid
    @5
    wn
    #
    @4
    @0
    wi
    #
    vy
    wal
    #
    @4
    @2
    wi
    #
    vy
    wal
    #
    @1
    @3
    @9
    @11
    wb
    @7
    @8
    @10
    vy
    @4
    @0
    @2
    @6
    pm5.74i
    albii
    a1i
    @0
    vy
    vz
    sb4b
    @2
    vy
    vz
    sb4b
    3bitr4d
    pm2.61i
    wph
    vx
    vz
    vy
    sbcom
    bitri
end
