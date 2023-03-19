include "cfrgr.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wrex.mm"
include "wex.mm"
include "cvv.mm"
include "wb.mm"
include "cvtx.mm"
include "fvexi.mm"
include "rabex2.mm"
include "hash1snb.mm"
include "ax-mp.mm"
include "wi.mm"
include "exsnrex.mm"
include "wss.mm"
include "ssrab3.mm"
include "ssrexv.mm"
include "frgrwopregasn.mm"
include "3expia.mm"
include "reximdva.mm"
include "syl5com.mm"
include "sylbi.mm"
include "com12.mm"
include "syl5bi.mm"
include "imp.mm"

theorem frgrwopreg1
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cD: class D
  let cE: class E
  let cG: class G
  let cK: class K
  let cV: class V
  let vb: setvar b
  let vy: setvar y
  let va: setvar a
  let cX: class X
  let cY: class Y
  assume frgrwopreg.v: |- V = ( Vtx ` G )
  assume frgrwopreg.d: |- D = ( VtxDeg ` G )
  assume frgrwopreg.a: |- A = { x e. V | ( D ` x ) = K }
  assume frgrwopreg.b: |- B = ( V \ A )
  assume frgrwopreg.e: |- E = ( Edg ` G )

  disjoint B x
  disjoint G x
  disjoint A v
  disjoint A w
  disjoint v w
  disjoint B v
  disjoint B w
  disjoint E v
  disjoint G v
  disjoint G w
  disjoint v x
  disjoint w x
  disjoint V w
  disjoint V v
  disjoint V x
  disjoint A x
  disjoint G x
  disjoint K x
  disjoint D x
  disjoint A b
  disjoint D y
  disjoint G a
  disjoint G b
  disjoint G y
  disjoint a b
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint V y
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y x
  assert |- ( ( G e. FriendGraph /\ ( # ` A ) = 1 ) -> E. v e. V A. w e. ( V \ { v } ) { v , w } e. E )

  proof
    cG
    cfrgr
    wcel
    #
    cA
    chash
    cfv
    c1
    wceq
    #
    vv
    cv
    #
    vw
    cv
    cpr
    cE
    wcel
    vw
    cV
    @2
    csn
    #
    cdif
    wral
    #
    vv
    cV
    wrex
    #
    @1
    cA
    @3
    wceq
    #
    vv
    wex
    #
    @0
    @5
    cA
    cvv
    wcel
    @1
    @7
    wb
    vx
    cv
    cD
    cfv
    cK
    wceq
    #
    vx
    cV
    cA
    frgrwopreg.a
    cV
    cG
    cvtx
    frgrwopreg.v
    fvexi
    rabex2
    cA
    cvv
    vv
    hash1snb
    ax-mp
    @7
    @0
    @5
    @7
    @6
    vv
    cA
    wrex
    #
    @0
    @5
    wi
    vv
    cA
    exsnrex
    @9
    @6
    vv
    cV
    wrex
    #
    @0
    @5
    cA
    cV
    wss
    @9
    @10
    wi
    @8
    vx
    cV
    cA
    frgrwopreg.a
    ssrab3
    @6
    vv
    cA
    cV
    ssrexv
    ax-mp
    @0
    @6
    @4
    vv
    cV
    @0
    @2
    cV
    wcel
    @6
    @4
    vx
    vw
    cA
    cB
    cD
    cE
    cG
    cK
    cV
    @2
    frgrwopreg.v
    frgrwopreg.d
    frgrwopreg.a
    frgrwopreg.b
    frgrwopreg.e
    frgrwopregasn
    3expia
    reximdva
    syl5com
    sylbi
    com12
    syl5bi
    imp
end
