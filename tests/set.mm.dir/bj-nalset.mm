include "wel.mm"
include "wn.mm"
include "wex.mm"
include "wal.mm"
include "alexn.mm"
include "wa.mm"
include "wb.mm"
include "ax-sep.mm"
include "weq.mm"
include "elequ1.mm"
include "elequ2.mm"
include "bitrd.mm"
include "notbid.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "bj-spvv.mm"
include "pclem6.mm"
include "syl.mm"
include "eximii.mm"
include "mpgbi.mm"

theorem bj-nalset
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint x z
  disjoint y z
  assert |- -. E. x A. y y e. x

  proof
    vy
    vx
    wel
    #
    wn
    #
    vy
    wex
    @0
    vy
    wal
    vx
    wex
    wn
    vx
    @0
    vx
    vy
    alexn
    vz
    vy
    wel
    #
    vz
    vx
    wel
    #
    vz
    vz
    wel
    #
    wn
    #
    wa
    #
    wb
    #
    vz
    wal
    #
    @1
    vy
    @5
    vz
    vy
    vx
    ax-sep
    @8
    vy
    vy
    wel
    #
    @0
    @9
    wn
    #
    wa
    #
    wb
    #
    @1
    @7
    @12
    vz
    vy
    vz
    vy
    weq
    #
    @2
    @9
    @6
    @11
    vz
    vy
    vy
    elequ1
    @13
    @3
    @0
    @5
    @10
    vz
    vy
    vx
    elequ1
    @13
    @4
    @9
    @13
    @4
    vy
    vz
    wel
    @9
    vz
    vy
    vz
    elequ1
    vz
    vy
    vy
    elequ2
    bitrd
    notbid
    anbi12d
    bibi12d
    bj-spvv
    @9
    @0
    pclem6
    syl
    eximii
    mpgbi
end
