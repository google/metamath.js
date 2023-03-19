include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wceq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "axacnd.mm"
include "19.3v.mm"
include "imbi1i.mm"
include "2albii.mm"
include "exbii.mm"
include "mpbi.mm"
include "equequ2.mm"
include "bibi2d.mm"
include "elequ2.mm"
include "anbi2d.mm"
include "elequ1.mm"
include "anbi12d.mm"
include "cbvexv.mm"
include "bibi1i.mm"
include "syl6bb.mm"
include "albidv.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "equequ1.mm"
include "bibi12d.mm"
include "cbvalv.mm"
include "imbi2i.mm"
include "mpbir.mm"

theorem zfcndac
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint u v
  disjoint t v
  disjoint t u
  assert |- E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) )

  proof
    vz
    cv
    #
    vw
    cv
    #
    wcel
    #
    @1
    vx
    cv
    #
    wcel
    #
    wa
    #
    vu
    cv
    #
    @1
    wcel
    #
    @1
    vt
    cv
    #
    wcel
    #
    wa
    #
    @6
    @8
    wcel
    #
    @8
    vy
    cv
    #
    wcel
    #
    wa
    #
    wa
    #
    vt
    wex
    #
    @6
    vv
    cv
    #
    wceq
    #
    wb
    #
    vu
    wal
    #
    vv
    wex
    #
    wi
    #
    vw
    wal
    vz
    wal
    #
    vy
    wex
    @5
    @5
    @0
    @3
    wcel
    #
    @3
    @12
    wcel
    #
    wa
    #
    wa
    #
    vx
    wex
    #
    @0
    @3
    wceq
    #
    wb
    #
    vz
    wal
    #
    vx
    wex
    #
    wi
    #
    vw
    wal
    vz
    wal
    #
    vy
    wex
    #
    @5
    vy
    wal
    #
    @32
    wi
    #
    vw
    wal
    vz
    wal
    #
    vy
    wex
    @35
    vy
    vz
    vw
    vx
    axacnd
    @38
    @34
    vy
    @37
    @33
    vz
    vw
    @36
    @5
    @32
    @5
    vy
    19.3v
    imbi1i
    2albii
    exbii
    mpbi
    @23
    @34
    vy
    @22
    @33
    vz
    vw
    @21
    @32
    @5
    @20
    @31
    vv
    vx
    @17
    @3
    wceq
    #
    @20
    @7
    @4
    wa
    #
    @6
    @3
    wcel
    #
    @25
    wa
    #
    wa
    #
    vx
    wex
    #
    @6
    @3
    wceq
    #
    wb
    #
    vu
    wal
    @31
    @39
    @19
    @46
    vu
    @39
    @19
    @16
    @45
    wb
    @46
    @39
    @18
    @45
    @16
    vv
    vx
    vu
    equequ2
    bibi2d
    @16
    @44
    @45
    @15
    @43
    vt
    vx
    @8
    @3
    wceq
    #
    @10
    @40
    @14
    @42
    @47
    @9
    @4
    @7
    vt
    vx
    vw
    elequ2
    anbi2d
    @47
    @11
    @41
    @13
    @25
    vt
    vx
    vu
    elequ2
    vt
    vx
    vy
    elequ1
    anbi12d
    anbi12d
    cbvexv
    bibi1i
    syl6bb
    albidv
    @46
    @30
    vu
    vz
    @6
    @0
    wceq
    #
    @44
    @28
    @45
    @29
    @48
    @43
    @27
    vx
    @48
    @40
    @5
    @42
    @26
    @48
    @7
    @2
    @4
    vu
    vz
    vw
    elequ1
    anbi1d
    @48
    @41
    @24
    @25
    vu
    vz
    vx
    elequ1
    anbi1d
    anbi12d
    exbidv
    vu
    vz
    vx
    equequ1
    bibi12d
    cbvalv
    syl6bb
    cbvexv
    imbi2i
    2albii
    exbii
    mpbir
end
