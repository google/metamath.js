include "wel.mm"
include "wa.mm"
include "wex.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "ax-ac.mm"
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
include "2albii.mm"
include "exbii.mm"
include "mpbi.mm"

theorem zfac
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
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint v x
  disjoint u x
  disjoint t x
  disjoint v y
  disjoint u y
  disjoint t y
  disjoint v z
  disjoint u z
  disjoint t z
  disjoint v w
  disjoint u w
  disjoint t w
  disjoint u v
  disjoint t v
  disjoint t u
  assert |- E. x A. y A. z ( ( y e. z /\ z e. w ) -> E. w A. y ( E. w ( ( y e. z /\ z e. w ) /\ ( y e. w /\ w e. x ) ) <-> y = w ) )

  proof
    vy
    vz
    wel
    #
    vz
    vw
    wel
    #
    wa
    #
    vu
    vz
    wel
    #
    vz
    vt
    wel
    #
    wa
    #
    vu
    vt
    wel
    #
    vt
    vx
    wel
    #
    wa
    #
    wa
    #
    vt
    wex
    #
    vu
    vv
    weq
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
    vz
    wal
    vy
    wal
    #
    vx
    wex
    @2
    @2
    vy
    vw
    wel
    #
    vw
    vx
    wel
    #
    wa
    #
    wa
    #
    vw
    wex
    #
    vy
    vw
    weq
    #
    wb
    #
    vy
    wal
    #
    vw
    wex
    #
    wi
    #
    vz
    wal
    vy
    wal
    #
    vx
    wex
    vw
    vx
    vy
    vz
    vv
    vu
    vt
    ax-ac
    @16
    @27
    vx
    @15
    @26
    vy
    vz
    @14
    @25
    @2
    @13
    @24
    vv
    vw
    vv
    vw
    weq
    #
    @13
    @3
    @1
    wa
    #
    vu
    vw
    wel
    #
    @18
    wa
    #
    wa
    #
    vw
    wex
    #
    vu
    vw
    weq
    #
    wb
    #
    vu
    wal
    @24
    @28
    @12
    @35
    vu
    @28
    @12
    @10
    @34
    wb
    @35
    @28
    @11
    @34
    @10
    vv
    vw
    vu
    equequ2
    bibi2d
    @10
    @33
    @34
    @9
    @32
    vt
    vw
    vt
    vw
    weq
    #
    @5
    @29
    @8
    @31
    @36
    @4
    @1
    @3
    vt
    vw
    vz
    elequ2
    anbi2d
    @36
    @6
    @30
    @7
    @18
    vt
    vw
    vu
    elequ2
    vt
    vw
    vx
    elequ1
    anbi12d
    anbi12d
    cbvexv
    bibi1i
    syl6bb
    albidv
    @35
    @23
    vu
    vy
    vu
    vy
    weq
    #
    @33
    @21
    @34
    @22
    @37
    @32
    @20
    vw
    @37
    @29
    @2
    @31
    @19
    @37
    @3
    @0
    @1
    vu
    vy
    vz
    elequ1
    anbi1d
    @37
    @30
    @17
    @18
    vu
    vy
    vw
    elequ1
    anbi1d
    anbi12d
    exbidv
    vu
    vy
    vw
    equequ1
    bibi12d
    cbvalv
    syl6bb
    cbvexv
    imbi2i
    2albii
    exbii
    mpbi
end
