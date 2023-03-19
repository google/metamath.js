include "wel.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wreu.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wex.mm"
include "wal.mm"
include "df-ral.mm"
include "19.23v.mm"
include "bitri.mm"
include "weq.mm"
include "biidd.mm"
include "cbvralv.mm"
include "n0.mm"
include "elequ2.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "reubii.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvreuv.mm"
include "imbi12i.mm"
include "3bitr4i.mm"
include "ralbii.mm"
include "exbii.mm"

theorem aceq2
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
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint v w
  disjoint u w
  disjoint u v
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint t w
  disjoint t v
  disjoint t u
  assert |- ( E. y A. z e. x A. w e. z E! v e. z E. u e. y ( z e. u /\ v e. u ) <-> E. y A. z e. x ( z =/= (/) -> E! w e. z E. v e. y ( z e. v /\ w e. v ) ) )

  proof
    vz
    vu
    wel
    #
    vv
    vu
    wel
    #
    wa
    #
    vu
    vy
    cv
    #
    wrex
    #
    vv
    vz
    cv
    #
    wreu
    #
    vw
    @5
    wral
    #
    vz
    vx
    cv
    #
    wral
    @5
    c0
    wne
    #
    vz
    vv
    wel
    #
    vw
    vv
    wel
    #
    wa
    #
    vv
    @3
    wrex
    #
    vw
    @5
    wreu
    #
    wi
    #
    vz
    @8
    wral
    vy
    @7
    @15
    vz
    @8
    @6
    vt
    @5
    wral
    #
    vt
    vz
    wel
    #
    vt
    wex
    #
    @6
    wi
    #
    @7
    @15
    @16
    @17
    @6
    wi
    vt
    wal
    @19
    @6
    vt
    @5
    df-ral
    @17
    @6
    vt
    19.23v
    bitri
    @6
    @6
    vw
    vt
    @5
    vw
    vt
    weq
    @6
    biidd
    cbvralv
    @9
    @18
    @14
    @6
    vt
    @5
    n0
    @14
    @0
    vw
    vu
    wel
    #
    wa
    #
    vu
    @3
    wrex
    #
    vw
    @5
    wreu
    @6
    @13
    @22
    vw
    @5
    @12
    @21
    vv
    vu
    @3
    vv
    vu
    weq
    @10
    @0
    @11
    @20
    vv
    vu
    vz
    elequ2
    vv
    vu
    vw
    elequ2
    anbi12d
    cbvrexv
    reubii
    @22
    @4
    vw
    vv
    @5
    vw
    vv
    weq
    #
    @21
    @2
    vu
    @3
    @23
    @20
    @1
    @0
    vw
    cv
    vv
    cv
    vu
    cv
    eleq1
    anbi2d
    rexbidv
    cbvreuv
    bitri
    imbi12i
    3bitr4i
    ralbii
    exbii
end
