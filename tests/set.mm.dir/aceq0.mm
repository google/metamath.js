include "wel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wreu.mm"
include "wral.mm"
include "wex.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "wi.mm"
include "aceq1.mm"
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
include "bitr4i.mm"

theorem aceq0
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
  assert |- ( E. y A. z e. x A. w e. z E! v e. z E. u e. y ( z e. u /\ v e. u ) <-> E. y A. z A. w ( ( z e. w /\ w e. x ) -> E. v A. u ( E. t ( ( u e. w /\ w e. t ) /\ ( u e. t /\ t e. y ) ) <-> u = v ) ) )

  proof
    vz
    vu
    wel
    vv
    vu
    wel
    wa
    vu
    vy
    cv
    wrex
    vv
    vz
    cv
    #
    wreu
    vw
    @0
    wral
    vz
    vx
    cv
    wral
    vy
    wex
    vz
    vw
    wel
    #
    vw
    vx
    wel
    #
    wa
    #
    @3
    vz
    vx
    wel
    #
    vx
    vy
    wel
    #
    wa
    #
    wa
    #
    vx
    wex
    #
    vz
    vx
    weq
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
    @3
    vu
    vw
    wel
    #
    vw
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
    vy
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
    vw
    wal
    vz
    wal
    #
    vy
    wex
    vx
    vy
    vz
    vw
    vv
    vu
    aceq1
    @28
    @14
    vy
    @27
    @13
    vz
    vw
    @26
    @12
    @3
    @25
    @11
    vv
    vx
    vv
    vx
    weq
    #
    @25
    @15
    @2
    wa
    #
    vu
    vx
    wel
    #
    @5
    wa
    #
    wa
    #
    vx
    wex
    #
    vu
    vx
    weq
    #
    wb
    #
    vu
    wal
    @11
    @29
    @24
    @36
    vu
    @29
    @24
    @22
    @35
    wb
    @36
    @29
    @23
    @35
    @22
    vv
    vx
    vu
    equequ2
    bibi2d
    @22
    @34
    @35
    @21
    @33
    vt
    vx
    vt
    vx
    weq
    #
    @17
    @30
    @20
    @32
    @37
    @16
    @2
    @15
    vt
    vx
    vw
    elequ2
    anbi2d
    @37
    @18
    @31
    @19
    @5
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
    @36
    @10
    vu
    vz
    vu
    vz
    weq
    #
    @34
    @8
    @35
    @9
    @38
    @33
    @7
    vx
    @38
    @30
    @3
    @32
    @6
    @38
    @15
    @1
    @2
    vu
    vz
    vw
    elequ1
    anbi1d
    @38
    @31
    @4
    @5
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
    bitr4i
end
