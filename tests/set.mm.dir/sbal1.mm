include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "sb4b.mm"
include "nfnae.mm"
include "wnf.mm"
include "nfeqf2.mm"
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

theorem sbal1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( -. A. x x = z -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) )

  proof
    vx
    vz
    weq
    vx
    wal
    wn
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
    @0
    @2
    wn
    #
    @7
    @0
    @8
    wa
    @4
    @1
    wph
    wi
    #
    vx
    wal
    #
    vy
    wal
    #
    @6
    @8
    @4
    @1
    @3
    wi
    #
    vy
    wal
    @0
    @11
    @3
    vy
    vz
    sb4b
    @0
    @12
    @10
    vy
    vx
    vz
    vy
    nfnae
    @0
    @1
    vx
    wnf
    #
    @12
    @10
    wb
    vx
    vz
    vy
    nfeqf2
    @13
    @10
    @12
    @1
    wph
    vx
    19.21t
    bicomd
    syl
    albid
    sylan9bbr
    @8
    @6
    @11
    wb
    @0
    @8
    @6
    @9
    vy
    wal
    #
    vx
    wal
    @11
    @8
    @5
    @14
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
    @9
    vx
    vy
    alcom
    syl6bb
    adantl
    bitr4d
    ex
    @2
    @3
    @4
    @6
    @1
    @3
    @4
    wb
    vy
    @3
    vy
    vz
    sbequ12
    sps
    wph
    @5
    vy
    vz
    vx
    @1
    wph
    @5
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
