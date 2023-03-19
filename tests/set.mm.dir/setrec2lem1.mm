include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "cab.mm"
include "wcel.mm"
include "cres.mm"
include "cfv.mm"
include "wceq.mm"
include "fvres.mm"
include "wn.mm"
include "c0.mm"
include "cdm.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseli.mm"
include "con3i.mm"
include "ndmfv.mm"
include "syl.mm"
include "vex.mm"
include "breq1.mm"
include "eubidv.mm"
include "elab.mm"
include "notbii.mm"
include "biimpi.mm"
include "tz6.12-2.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem setrec2lem1
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let va: setvar a
  let vk: setvar k

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint a x
  disjoint a y
  disjoint k x
  assert |- ( ( F |` { x | E! y x F y } ) ` a ) = ( F ` a )

  proof
    va
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    vy
    weu
    #
    vx
    cab
    #
    wcel
    #
    @0
    cF
    @5
    cres
    #
    cfv
    #
    @0
    cF
    cfv
    #
    wceq
    @0
    @5
    cF
    fvres
    @6
    wn
    #
    @8
    c0
    @9
    @10
    @0
    @7
    cdm
    #
    wcel
    #
    wn
    @8
    c0
    wceq
    @12
    @6
    @11
    @5
    @0
    @11
    @5
    cF
    cdm
    #
    cin
    @5
    cF
    @5
    dmres
    @5
    @13
    inss1
    eqsstri
    sseli
    con3i
    @0
    @7
    ndmfv
    syl
    @10
    @0
    @2
    cF
    wbr
    #
    vy
    weu
    #
    wn
    #
    @9
    c0
    wceq
    @10
    @16
    @6
    @15
    @4
    @15
    vx
    @0
    va
    vex
    @1
    @0
    wceq
    @3
    @14
    vy
    @1
    @0
    @2
    cF
    breq1
    eubidv
    elab
    notbii
    biimpi
    vy
    @0
    cF
    tz6.12-2
    syl
    eqtr4d
    pm2.61i
end
