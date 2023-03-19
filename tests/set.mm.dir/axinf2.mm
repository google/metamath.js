include "c0.mm"
include "cv.mm"
include "wcel.mm"
include "wel.mm"
include "csuc.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wex.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "com.mm"
include "peano1.mm"
include "peano2.mm"
include "ax-gen.mm"
include "zfinf.mm"
include "inf2.mm"
include "inf3.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "albidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "mp2an.mm"
include "wrex.mm"
include "0el.mm"
include "df-rex.mm"
include "bitri.mm"
include "sucel.mm"
include "imbi2i.mm"
include "albii.mm"
include "anbi12i.mm"
include "exbii.mm"
include "mpbi.mm"

theorem axinf2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  assert |- E. x ( E. y ( y e. x /\ A. z -. z e. y ) /\ A. y ( y e. x -> E. z ( z e. x /\ A. w ( w e. z <-> ( w e. y \/ w = y ) ) ) ) )

  proof
    c0
    vx
    cv
    #
    wcel
    #
    vy
    vx
    wel
    #
    vy
    cv
    #
    csuc
    #
    @0
    wcel
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    vx
    wex
    #
    @2
    vz
    vy
    wel
    wn
    vz
    wal
    #
    wa
    vy
    wex
    #
    @2
    vz
    vx
    wel
    vw
    vz
    wel
    vw
    vy
    wel
    vw
    cv
    @3
    wceq
    wo
    wb
    vw
    wal
    #
    wa
    vz
    wex
    #
    wi
    #
    vy
    wal
    #
    wa
    #
    vx
    wex
    c0
    com
    wcel
    #
    @3
    com
    wcel
    #
    @4
    com
    wcel
    #
    wi
    #
    vy
    wal
    #
    @9
    peano1
    @20
    vy
    @3
    peano2
    ax-gen
    @8
    @17
    @21
    wa
    vx
    com
    vx
    vx
    vy
    vz
    vx
    vy
    vz
    zfinf
    inf2
    inf3
    @0
    com
    wceq
    #
    @1
    @17
    @7
    @21
    @0
    com
    c0
    eleq2
    @22
    @6
    @20
    vy
    @22
    @2
    @18
    @5
    @19
    @0
    com
    @3
    eleq2
    @0
    com
    @4
    eleq2
    imbi12d
    albidv
    anbi12d
    spcev
    mp2an
    @8
    @16
    vx
    @1
    @11
    @7
    @15
    @1
    @10
    vy
    @0
    wrex
    @11
    vy
    vz
    @0
    0el
    @10
    vy
    @0
    df-rex
    bitri
    @6
    @14
    vy
    @5
    @13
    @2
    @5
    @12
    vz
    @0
    wrex
    @13
    vz
    vw
    @3
    @0
    sucel
    @12
    vz
    @0
    df-rex
    bitri
    imbi2i
    albii
    anbi12i
    exbii
    mpbi
end
