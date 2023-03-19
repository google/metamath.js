include "cfrgr.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wne.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "w3o.mm"
include "wo.mm"
include "wi.mm"
include "frgrregorufr0.mm"
include "orc.mm"
include "a1d.mm"
include "wa.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "rspcva.mm"
include "wn.mm"
include "df-ne.mm"
include "pm2.21.mm"
include "sylbi.mm"
include "syl.mm"
include "ancoms.mm"
include "rexlimdva.mm"
include "olc.mm"
include "3jaoi.mm"

theorem frgrregorufr
  let vw: setvar w
  let vv: setvar v
  let cD: class D
  let cE: class E
  let cG: class G
  let cK: class K
  let cV: class V
  let va: setvar a
  let vx: setvar x
  let vy: setvar y
  assume frgrregorufr0.v: |- V = ( Vtx ` G )
  assume frgrregorufr0.e: |- E = ( Edg ` G )
  assume frgrregorufr0.d: |- D = ( VtxDeg ` G )

  disjoint D v
  disjoint D w
  disjoint v w
  disjoint E v
  disjoint G v
  disjoint G w
  disjoint K v
  disjoint K w
  disjoint V v
  disjoint V w
  disjoint D a
  disjoint a v
  disjoint E a
  disjoint K a
  disjoint V a
  disjoint a w
  disjoint D x
  disjoint D y
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint E y
  disjoint G y
  disjoint K x
  disjoint K y
  disjoint V x
  disjoint V y
  assert |- ( G e. FriendGraph -> ( E. a e. V ( D ` a ) = K -> ( A. v e. V ( D ` v ) = K \/ E. v e. V A. w e. ( V \ { v } ) { v , w } e. E ) ) )

  proof
    cG
    cfrgr
    wcel
    vv
    cv
    #
    cD
    cfv
    #
    cK
    wceq
    vv
    cV
    wral
    #
    @1
    cK
    wne
    #
    vv
    cV
    wral
    #
    @0
    vw
    cv
    cpr
    cE
    wcel
    vw
    cV
    @0
    csn
    cdif
    wral
    vv
    cV
    wrex
    #
    w3o
    va
    cv
    #
    cD
    cfv
    #
    cK
    wceq
    #
    va
    cV
    wrex
    #
    @2
    @5
    wo
    #
    wi
    #
    vw
    vv
    cD
    cE
    cG
    cK
    cV
    frgrregorufr0.v
    frgrregorufr0.e
    frgrregorufr0.d
    frgrregorufr0
    @2
    @11
    @4
    @5
    @2
    @10
    @9
    @2
    @5
    orc
    a1d
    @4
    @8
    @10
    va
    cV
    @6
    cV
    wcel
    #
    @4
    @8
    @10
    wi
    #
    @12
    @4
    wa
    @7
    cK
    wne
    #
    @13
    @3
    @14
    vv
    @6
    cV
    @0
    @6
    wceq
    @1
    @7
    cK
    @0
    @6
    cD
    fveq2
    neeq1d
    rspcva
    @14
    @8
    wn
    @13
    @7
    cK
    df-ne
    @8
    @10
    pm2.21
    sylbi
    syl
    ancoms
    rexlimdva
    @5
    @10
    @9
    @5
    @2
    olc
    a1d
    3jaoi
    syl
end
