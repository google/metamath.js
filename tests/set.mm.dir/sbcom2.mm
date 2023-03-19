include "weq.mm"
include "wex.mm"
include "wsb.mm"
include "wb.mm"
include "ax6ev.mm"
include "wi.mm"
include "wa.mm"
include "wal.mm"
include "2sb6.mm"
include "alcom.mm"
include "ancomst.mm"
include "2albii.mm"
include "3bitri.mm"
include "bitr4i.mm"
include "nfv.mm"
include "sbequ.mm"
include "sbbid.mm"
include "syl5bbr.mm"
include "sylan9bb.mm"
include "sylan9bbr.mm"
include "bitr3d.mm"
include "ex.mm"
include "exlimdv.mm"
include "exlimiv.mm"
include "mp2.mm"

theorem sbcom2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vv: setvar v

  disjoint x z
  disjoint w x
  disjoint y z
  disjoint u v
  disjoint u x
  disjoint u w
  disjoint v x
  disjoint v w
  disjoint u y
  disjoint u z
  disjoint v y
  disjoint v z
  disjoint ph u
  disjoint ph v
  assert |- ( [ w / z ] [ y / x ] ph <-> [ y / x ] [ w / z ] ph )

  proof
    vu
    vy
    weq
    #
    vu
    wex
    vv
    vw
    weq
    #
    vv
    wex
    #
    wph
    vx
    vy
    wsb
    #
    vz
    vw
    wsb
    #
    wph
    vz
    vw
    wsb
    #
    vx
    vy
    wsb
    #
    wb
    #
    vu
    vy
    ax6ev
    vv
    vw
    ax6ev
    @0
    @2
    @7
    wi
    vu
    @0
    @1
    @7
    vv
    @0
    @1
    @7
    @0
    @1
    wa
    wph
    vz
    vv
    wsb
    #
    vx
    vu
    wsb
    #
    @4
    @6
    @0
    @9
    @3
    vz
    vv
    wsb
    #
    @1
    @4
    @9
    wph
    vx
    vu
    wsb
    #
    vz
    vv
    wsb
    #
    @0
    @10
    @12
    vx
    vu
    weq
    #
    vz
    vv
    weq
    #
    wa
    wph
    wi
    #
    vz
    wal
    vx
    wal
    #
    @9
    @12
    @14
    @13
    wa
    wph
    wi
    #
    vx
    wal
    vz
    wal
    @17
    vz
    wal
    vx
    wal
    @16
    wph
    vz
    vx
    vv
    vu
    2sb6
    @17
    vz
    vx
    alcom
    @17
    @15
    vx
    vz
    @14
    @13
    wph
    ancomst
    2albii
    3bitri
    wph
    vx
    vz
    vu
    vv
    2sb6
    bitr4i
    @0
    @11
    @3
    vz
    vv
    @0
    vz
    nfv
    wph
    vu
    vy
    vx
    sbequ
    sbbid
    syl5bbr
    @3
    vv
    vw
    vz
    sbequ
    sylan9bb
    @1
    @9
    @5
    vx
    vu
    wsb
    @0
    @6
    @1
    @8
    @5
    vx
    vu
    @1
    vx
    nfv
    wph
    vv
    vw
    vz
    sbequ
    sbbid
    @5
    vu
    vy
    vx
    sbequ
    sylan9bbr
    bitr3d
    ex
    exlimdv
    exlimiv
    mp2
end
