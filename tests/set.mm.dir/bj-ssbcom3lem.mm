include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wssb.mm"
include "equequ2.mm"
include "imbi1d.mm"
include "pm5.74i.mm"
include "albii.mm"
include "19.21v.mm"
include "3bitr3i.mm"
include "bj-ssb1.mm"
include "bj-ssbbii.mm"
include "bitri.mm"
include "3bitr4i.mm"

theorem bj-ssbcom3lem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t

  disjoint x y
  disjoint t x
  disjoint t y
  assert |- ( [b t /b y ]b [b y /b x ]b ph <-> [b t /b y ]b [b t /b x ]b ph )

  proof
    vy
    vt
    weq
    #
    vx
    vy
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    vy
    wal
    #
    @0
    vx
    vt
    weq
    #
    wph
    wi
    #
    vx
    wal
    #
    wi
    #
    vy
    wal
    #
    wph
    vx
    vy
    wssb
    #
    vy
    vt
    wssb
    #
    wph
    vx
    vt
    wssb
    #
    vy
    vt
    wssb
    #
    @4
    @9
    vy
    @0
    @2
    wi
    #
    vx
    wal
    @0
    @7
    wi
    #
    vx
    wal
    @4
    @9
    @15
    @16
    vx
    @0
    @2
    @7
    @0
    @1
    @6
    wph
    vy
    vt
    vx
    equequ2
    imbi1d
    pm5.74i
    albii
    @0
    @2
    vx
    19.21v
    @0
    @7
    vx
    19.21v
    3bitr3i
    albii
    @12
    @3
    vy
    vt
    wssb
    @5
    @11
    @3
    vy
    vt
    wph
    vx
    vy
    bj-ssb1
    bj-ssbbii
    @3
    vy
    vt
    bj-ssb1
    bitri
    @14
    @8
    vy
    vt
    wssb
    @10
    @13
    @8
    vy
    vt
    wph
    vx
    vt
    bj-ssb1
    bj-ssbbii
    @8
    vy
    vt
    bj-ssb1
    bitri
    3bitr4i
end
