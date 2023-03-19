include "wcel.mm"
include "cfv.mm"
include "wne.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "cv.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "notbid.mm"
include "cdif.mm"
include "crab.mm"
include "difeq2i.mm"
include "notrab.mm"
include "3eqtri.mm"
include "elrab2.mm"
include "eqeq2.mm"
include "neqne.mm"
include "necomd.mm"
include "syl6bir.mm"
include "simplbiim.mm"
include "com12.mm"
include "impcom.mm"

theorem frgrwopreglem3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cG: class G
  let cK: class K
  let cV: class V
  let cX: class X
  let cY: class Y
  assume frgrwopreg.v: |- V = ( Vtx ` G )
  assume frgrwopreg.d: |- D = ( VtxDeg ` G )
  assume frgrwopreg.a: |- A = { x e. V | ( D ` x ) = K }
  assume frgrwopreg.b: |- B = ( V \ A )

  disjoint V x
  disjoint A x
  disjoint G x
  disjoint K x
  disjoint D x
  disjoint X x
  disjoint Y x
  assert |- ( ( X e. A /\ Y e. B ) -> ( D ` X ) =/= ( D ` Y ) )

  proof
    cY
    cB
    wcel
    #
    cX
    cA
    wcel
    #
    cX
    cD
    cfv
    #
    cY
    cD
    cfv
    #
    wne
    #
    @0
    cY
    cV
    wcel
    @3
    cK
    wceq
    #
    wn
    #
    @1
    @4
    wi
    vx
    cv
    #
    cD
    cfv
    #
    cK
    wceq
    #
    wn
    #
    @6
    vx
    cY
    cV
    cB
    @7
    cY
    wceq
    #
    @9
    @5
    @11
    @8
    @3
    cK
    @7
    cY
    cD
    fveq2
    eqeq1d
    notbid
    cB
    cV
    cA
    cdif
    cV
    @9
    vx
    cV
    crab
    #
    cdif
    @10
    vx
    cV
    crab
    frgrwopreg.b
    cA
    @12
    cV
    frgrwopreg.a
    difeq2i
    @9
    vx
    cV
    notrab
    3eqtri
    elrab2
    @1
    @6
    @4
    @1
    cX
    cV
    wcel
    @2
    cK
    wceq
    #
    @6
    @4
    wi
    @9
    @13
    vx
    cX
    cV
    cA
    @7
    cX
    wceq
    @8
    @2
    cK
    @7
    cX
    cD
    fveq2
    eqeq1d
    frgrwopreg.a
    elrab2
    @13
    @6
    @3
    @2
    wceq
    #
    wn
    #
    @4
    @13
    @14
    @5
    @2
    cK
    @3
    eqeq2
    notbid
    @15
    @3
    @2
    @3
    @2
    neqne
    necomd
    syl6bir
    simplbiim
    com12
    simplbiim
    impcom
end
