include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "wb.mm"
include "wa.mm"
include "wi.mm"
include "sb4b.mm"
include "adantl.mm"
include "nfnae.mm"
include "albid.mm"
include "alcom.mm"
include "wnf.mm"
include "nfeqf1.mm"
include "19.21t.mm"
include "syl.mm"
include "syl5bb.mm"
include "sylan9bbr.mm"
include "bitr4d.mm"
include "ex.mm"
include "sbid.mm"
include "drsb2.mm"
include "syl5bbr.mm"
include "dral2.mm"
include "bitr3d.mm"
include "pm2.61d2.mm"

theorem sbal2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x z
  assert |- ( -. A. x x = y -> ( [ z / y ] A. x ph <-> A. x [ z / y ] ph ) )

  proof
    vx
    vy
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
    @3
    wi
    #
    vy
    wal
    #
    @6
    @8
    @4
    @10
    wb
    @0
    @3
    vy
    vz
    sb4b
    adantl
    @8
    @6
    @1
    wph
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    @0
    @10
    @8
    @5
    @12
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
    @13
    @11
    vx
    wal
    #
    vy
    wal
    @0
    @10
    @11
    vx
    vy
    alcom
    @0
    @14
    @9
    vy
    vx
    vy
    vy
    nfnae
    @0
    @1
    vx
    wnf
    @14
    @9
    wb
    vx
    vy
    vz
    nfeqf1
    @1
    wph
    vx
    19.21t
    syl
    albid
    syl5bb
    sylan9bbr
    bitr4d
    ex
    @2
    @3
    @4
    @6
    @3
    @3
    vy
    vy
    wsb
    @2
    @4
    @3
    vy
    sbid
    @3
    vy
    vz
    vy
    drsb2
    syl5bbr
    wph
    @5
    vy
    vz
    vx
    wph
    wph
    vy
    vy
    wsb
    @2
    @5
    wph
    vy
    sbid
    wph
    vy
    vz
    vy
    drsb2
    syl5bbr
    dral2
    bitr3d
    pm2.61d2
end
