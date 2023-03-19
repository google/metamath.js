include "wcel.mm"
include "wel.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "wsbc.mm"
include "cv.mm"
include "wtr.mm"
include "sbcal.mm"
include "sbcim2g.mm"
include "wb.mm"
include "sbcg.mm"
include "sbcel2gv.mm"
include "imbi13.mm"
include "syl3c.mm"
include "bitrd.mm"
include "pm3.31.mm"
include "pm3.3.mm"
include "impbii.mm"
include "sbcbii.mm"
include "3bitr3g.mm"
include "albidv.mm"
include "syl5bb.mm"
include "dftr2.mm"
include "3bitr4g.mm"

theorem trsbc
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint V y
  disjoint V z
  assert |- ( A e. V -> ( [. A / x ]. Tr x <-> Tr A ) )

  proof
    cA
    cV
    wcel
    #
    vz
    vy
    wel
    #
    vy
    vx
    wel
    #
    wa
    vz
    vx
    wel
    #
    wi
    #
    vy
    wal
    #
    vz
    wal
    #
    vx
    cA
    wsbc
    #
    @1
    vy
    cv
    #
    cA
    wcel
    #
    wa
    vz
    cv
    #
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    vz
    wal
    #
    vx
    cv
    #
    wtr
    #
    vx
    cA
    wsbc
    cA
    wtr
    @7
    @5
    vx
    cA
    wsbc
    #
    vz
    wal
    @0
    @14
    @5
    vz
    vx
    cA
    sbcal
    @0
    @17
    @13
    vz
    @17
    @4
    vx
    cA
    wsbc
    #
    vy
    wal
    @0
    @13
    @4
    vy
    vx
    cA
    sbcal
    @0
    @18
    @12
    vy
    @0
    @1
    @2
    @3
    wi
    wi
    #
    vx
    cA
    wsbc
    #
    @1
    @9
    @11
    wi
    wi
    #
    @18
    @12
    @0
    @20
    @1
    vx
    cA
    wsbc
    #
    @2
    vx
    cA
    wsbc
    #
    @3
    vx
    cA
    wsbc
    #
    wi
    wi
    #
    @21
    @1
    @2
    @3
    vx
    cA
    cV
    sbcim2g
    @0
    @22
    @1
    wb
    @23
    @9
    wb
    @24
    @11
    wb
    @25
    @21
    wb
    @1
    vx
    cA
    cV
    sbcg
    vx
    @8
    cA
    cV
    sbcel2gv
    vx
    @10
    cA
    cV
    sbcel2gv
    @22
    @1
    @23
    @9
    @24
    @11
    imbi13
    syl3c
    bitrd
    @19
    @4
    vx
    cA
    @19
    @4
    @1
    @2
    @3
    pm3.31
    @1
    @2
    @3
    pm3.3
    impbii
    sbcbii
    @21
    @12
    @1
    @9
    @11
    pm3.31
    @1
    @9
    @11
    pm3.3
    impbii
    3bitr3g
    albidv
    syl5bb
    albidv
    syl5bb
    @16
    @6
    vx
    cA
    vz
    vy
    @15
    dftr2
    sbcbii
    vz
    vy
    cA
    dftr2
    3bitr4g
end
