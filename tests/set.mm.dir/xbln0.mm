include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "elbl.mm"
include "cle.mm"
include "xmetge0.mm"
include "3expa.mm"
include "3adantl3.mm"
include "wi.mm"
include "0xr.mm"
include "a1i.mm"
include "xmetcl.mm"
include "simpl3.mm"
include "xrlelttr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "expimpd.mm"
include "sylbid.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "xblcntr.mm"
include "ne0i.mm"
include "syl.mm"
include "expr.mm"
include "3impa.mm"
include "impbid.mm"

theorem xbln0
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> ( ( P ( ball ` D ) R ) =/= (/) <-> 0 < R ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    w3a
    #
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    c0
    wne
    #
    cc0
    cR
    clt
    wbr
    #
    @5
    vx
    cv
    #
    @4
    wcel
    #
    vx
    wex
    @3
    @6
    vx
    @4
    n0
    @3
    @8
    @6
    vx
    @3
    @8
    @7
    cX
    wcel
    #
    cP
    @7
    cD
    co
    #
    cR
    clt
    wbr
    #
    wa
    @6
    @7
    cD
    cP
    cR
    cX
    elbl
    @3
    @9
    @11
    @6
    @3
    @9
    wa
    #
    cc0
    @10
    cle
    wbr
    #
    @11
    @6
    @0
    @1
    @9
    @13
    @2
    @0
    @1
    @9
    @13
    cP
    @7
    cD
    cX
    xmetge0
    3expa
    3adantl3
    @12
    cc0
    cxr
    wcel
    #
    @10
    cxr
    wcel
    #
    @2
    @13
    @11
    wa
    @6
    wi
    @14
    @12
    0xr
    a1i
    @0
    @1
    @9
    @15
    @2
    @0
    @1
    @9
    @15
    cP
    @7
    cD
    cX
    xmetcl
    3expa
    3adantl3
    @0
    @1
    @2
    @9
    simpl3
    cc0
    @10
    cR
    xrlelttr
    syl3anc
    mpand
    expimpd
    sylbid
    exlimdv
    syl5bi
    @0
    @1
    @2
    @6
    @5
    wi
    @0
    @1
    wa
    @2
    @6
    @5
    @0
    @1
    @2
    @6
    wa
    #
    @5
    @0
    @1
    @16
    w3a
    cP
    @4
    wcel
    @5
    cD
    cP
    cR
    cX
    xblcntr
    @4
    cP
    ne0i
    syl
    3expa
    expr
    3impa
    impbid
end
