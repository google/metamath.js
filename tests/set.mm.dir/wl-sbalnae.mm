include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wa.mm"
include "wsb.mm"
include "wb.mm"
include "wi.mm"
include "sb4b.mm"
include "nfnae.mm"
include "nfan.mm"
include "wnf.mm"
include "nfeqf.mm"
include "19.21t.mm"
include "bicomd.mm"
include "syl.mm"
include "albid.mm"
include "sylan9bbr.mm"
include "alcom.mm"
include "syl6bb.mm"
include "adantl.mm"
include "bitr4d.mm"
include "ex.mm"
include "sbequ12.mm"
include "sps.mm"
include "dral2.mm"
include "bitr3d.mm"
include "pm2.61d2.mm"

theorem wl-sbalnae
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( -. A. x x = y /\ -. A. x x = z ) -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    #
    vx
    vz
    weq
    vx
    wal
    wn
    #
    wa
    #
    vy
    vz
    weq
    #
    vy
    wal
    #
    wph
    vx
    wal
    #
    vy
    vz
    wsb
    #
    wph
    vy
    vz
    wsb
    #
    vx
    wal
    #
    wb
    #
    @2
    @4
    wn
    #
    @9
    @2
    @10
    wa
    @6
    @3
    wph
    wi
    #
    vx
    wal
    #
    vy
    wal
    #
    @8
    @10
    @6
    @3
    @5
    wi
    #
    vy
    wal
    @2
    @13
    @5
    vy
    vz
    sb4b
    @2
    @14
    @12
    vy
    @0
    @1
    vy
    vx
    vy
    vy
    nfnae
    vx
    vz
    vy
    nfnae
    nfan
    @2
    @3
    vx
    wnf
    #
    @14
    @12
    wb
    vy
    vz
    vx
    nfeqf
    @15
    @12
    @14
    @3
    wph
    vx
    19.21t
    bicomd
    syl
    albid
    sylan9bbr
    @10
    @8
    @13
    wb
    @2
    @10
    @8
    @11
    vy
    wal
    #
    vx
    wal
    @13
    @10
    @7
    @16
    vx
    vy
    vz
    vx
    nfnae
    wph
    vy
    vz
    sb4b
    albid
    @11
    vx
    vy
    alcom
    syl6bb
    adantl
    bitr4d
    ex
    @4
    @5
    @6
    @8
    @3
    @5
    @6
    wb
    vy
    @5
    vy
    vz
    sbequ12
    sps
    wph
    @7
    vy
    vz
    vx
    @3
    wph
    @7
    wb
    vy
    wph
    vy
    vz
    sbequ12
    sps
    dral2
    bitr3d
    pm2.61d2
end
