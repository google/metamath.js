include "wcel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "wbr.mm"
include "wex.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "cab.mm"
include "suppval.mm"
include "df-rab.mm"
include "vex.mm"
include "eldm.mm"
include "df-sn.mm"
include "neeq2i.mm"
include "cvv.mm"
include "imasng.mm"
include "ax-mp.mm"
include "neeq1i.mm"
include "nabbi.mm"
include "3bitr4i.mm"
include "anbi12i.mm"
include "abbii.mm"
include "eqtri.mm"
include "a1i.mm"
include "df-ne.mm"
include "bicomi.mm"
include "bibi2i.mm"
include "exbii.mm"
include "anbi2i.mm"
include "3eqtrd.mm"

theorem suppvalbr
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cV: class V
  let cW: class W
  let cZ: class Z

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint Z x
  disjoint Z y
  assert |- ( ( R e. V /\ Z e. W ) -> ( R supp Z ) = { x | ( E. y x R y /\ E. y ( x R y <-> y =/= Z ) ) } )

  proof
    cR
    cV
    wcel
    cZ
    cW
    wcel
    wa
    #
    cR
    cZ
    csupp
    co
    cR
    vx
    cv
    #
    csn
    cima
    #
    cZ
    csn
    #
    wne
    #
    vx
    cR
    cdm
    #
    crab
    #
    @1
    vy
    cv
    #
    cR
    wbr
    #
    vy
    wex
    #
    @8
    @7
    cZ
    wceq
    #
    wn
    #
    wb
    #
    vy
    wex
    #
    wa
    #
    vx
    cab
    #
    @9
    @8
    @7
    cZ
    wne
    #
    wb
    #
    vy
    wex
    #
    wa
    #
    vx
    cab
    #
    vx
    cV
    cW
    cR
    cZ
    suppval
    @6
    @15
    wceq
    @0
    @6
    @1
    @5
    wcel
    #
    @4
    wa
    #
    vx
    cab
    @15
    @4
    vx
    @5
    df-rab
    @22
    @14
    vx
    @21
    @9
    @4
    @13
    vy
    @1
    cR
    vx
    vex
    #
    eldm
    @8
    vy
    cab
    #
    @3
    wne
    @24
    @10
    vy
    cab
    #
    wne
    @4
    @13
    @3
    @25
    @24
    vy
    cZ
    df-sn
    neeq2i
    @2
    @24
    @3
    @1
    cvv
    wcel
    @2
    @24
    wceq
    @23
    vy
    @1
    cvv
    cR
    imasng
    ax-mp
    neeq1i
    @8
    @10
    vy
    nabbi
    3bitr4i
    anbi12i
    abbii
    eqtri
    a1i
    @15
    @20
    wceq
    @0
    @14
    @19
    vx
    @13
    @18
    @9
    @12
    @17
    vy
    @11
    @16
    @8
    @16
    @11
    @7
    cZ
    df-ne
    bicomi
    bibi2i
    exbii
    anbi2i
    abbii
    a1i
    3eqtrd
end
