include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "ax-1.mm"
include "axc4i-o.mm"
include "a1i.mm"
include "biidd.mm"
include "dral1-o.mm"
include "imbi2d.mm"
include "dral2-o.mm"
include "3imtr4d.mm"
include "aecoms-o.mm"
include "a1d.mm"
include "wa.mm"
include "simplr.mm"
include "dveeq1-o.mm"
include "naecoms-o.mm"
include "imp.mm"
include "adantlr.mm"
include "hbnae-o.mm"
include "hba1-o.mm"
include "hban.mm"
include "ax-c5.mm"
include "sylan2.mm"
include "alimdh.mm"
include "syl2anc.mm"
include "ax-11.mm"
include "wnf.mm"
include "wb.mm"
include "nf5dh.mm"
include "19.21t.mm"
include "syl.mm"
include "albidh.mm"
include "syl5ib.mm"
include "ad2antrr.mm"
include "syld.mm"
include "exp31.mm"
include "pm2.61i.mm"

theorem ax12inda2ALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume ax12inda2.1: |- ( -. A. x x = y -> ( x = y -> ( ph -> A. x ( x = y -> ph ) ) ) )

  disjoint y z
  assert |- ( -. A. x x = y -> ( x = y -> ( A. z ph -> A. x ( x = y -> A. z ph ) ) ) )

  proof
    vx
    vz
    weq
    vx
    wal
    #
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    @1
    wph
    vz
    wal
    #
    @1
    @3
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    #
    wi
    @0
    @7
    @2
    @0
    @6
    @1
    @6
    vz
    vx
    vz
    vx
    weq
    vz
    wal
    #
    wph
    vx
    wal
    #
    @1
    @9
    wi
    #
    vx
    wal
    #
    @3
    @5
    @9
    @11
    wi
    @8
    wph
    @10
    vx
    @9
    @1
    ax-1
    axc4i-o
    a1i
    wph
    wph
    vz
    vx
    @8
    wph
    biidd
    dral1-o
    #
    @4
    @10
    vz
    vx
    vx
    @8
    @3
    @9
    @1
    @12
    imbi2d
    dral2-o
    3imtr4d
    aecoms-o
    a1d
    a1d
    @0
    wn
    #
    @2
    @1
    @6
    @13
    @2
    wa
    @1
    wa
    #
    @3
    @1
    wph
    wi
    #
    vx
    wal
    #
    vz
    wal
    #
    @5
    @14
    @2
    @1
    vz
    wal
    #
    @3
    @17
    wi
    @13
    @2
    @1
    simplr
    @13
    @1
    @18
    @2
    @13
    @1
    @18
    @1
    @18
    wi
    vz
    vx
    vz
    vx
    vy
    dveeq1-o
    naecoms-o
    #
    imp
    adantlr
    @2
    @18
    wa
    wph
    @16
    vz
    @2
    @18
    vz
    vx
    vy
    vz
    hbnae-o
    @1
    vz
    hba1-o
    hban
    @18
    @2
    @1
    wph
    @16
    wi
    #
    @1
    vz
    ax-c5
    @2
    @1
    @20
    ax12inda2.1
    imp
    sylan2
    alimdh
    syl2anc
    @13
    @17
    @5
    wi
    @2
    @1
    @17
    @15
    vz
    wal
    #
    vx
    wal
    @13
    @5
    @15
    vz
    vx
    ax-11
    @13
    @21
    @4
    vx
    vx
    vz
    vx
    hbnae-o
    @13
    @1
    vz
    wnf
    @21
    @4
    wb
    @13
    @1
    vz
    vx
    vz
    vz
    hbnae-o
    @19
    nf5dh
    @1
    wph
    vz
    19.21t
    syl
    albidh
    syl5ib
    ad2antrr
    syld
    exp31
    pm2.61i
end
