include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "cpr.mm"
include "crio.mm"
include "cnbgr.mm"
include "co.mm"
include "cin.mm"
include "cvv.mm"
include "wceq.mm"
include "simpr.mm"
include "riotaex.mm"
include "fvmpt2.mm"
include "sylancl.mm"
include "sneqd.mm"
include "frgrncvvdeqlem3.mm"
include "eqtrd.mm"

theorem frgrncvvdeqlem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vn: setvar n
  assume frgrncvvdeq.v1: |- V = ( Vtx ` G )
  assume frgrncvvdeq.e: |- E = ( Edg ` G )
  assume frgrncvvdeq.nx: |- D = ( G NeighbVtx X )
  assume frgrncvvdeq.ny: |- N = ( G NeighbVtx Y )
  assume frgrncvvdeq.x: |- ( ph -> X e. V )
  assume frgrncvvdeq.y: |- ( ph -> Y e. V )
  assume frgrncvvdeq.ne: |- ( ph -> X =/= Y )
  assume frgrncvvdeq.xy: |- ( ph -> Y e/ D )
  assume frgrncvvdeq.f: |- ( ph -> G e. FriendGraph )
  assume frgrncvvdeq.a: |- A = ( x e. D |-> ( iota_ y e. N { x , y } e. E ) )

  disjoint G y
  disjoint V y
  disjoint Y y
  disjoint x y
  disjoint E y
  disjoint N y
  disjoint D x
  disjoint N x
  disjoint ph x
  disjoint D n
  disjoint E n
  disjoint n y
  disjoint G n
  disjoint N n
  disjoint V n
  disjoint Y n
  disjoint n ph
  disjoint n x
  assert |- ( ( ph /\ x e. D ) -> { ( A ` x ) } = ( ( G NeighbVtx x ) i^i N ) )

  proof
    wph
    vx
    cv
    #
    cD
    wcel
    #
    wa
    #
    @0
    cA
    cfv
    #
    csn
    @0
    vy
    cv
    cpr
    cE
    wcel
    #
    vy
    cN
    crio
    #
    csn
    cG
    @0
    cnbgr
    co
    cN
    cin
    @2
    @3
    @5
    @2
    @1
    @5
    cvv
    wcel
    @3
    @5
    wceq
    wph
    @1
    simpr
    @4
    vy
    cN
    riotaex
    vx
    cD
    @5
    cvv
    cA
    frgrncvvdeq.a
    fvmpt2
    sylancl
    sneqd
    wph
    vx
    vy
    cA
    cD
    cE
    cG
    cN
    cV
    cX
    cY
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frgrncvvdeq.nx
    frgrncvvdeq.ny
    frgrncvvdeq.x
    frgrncvvdeq.y
    frgrncvvdeq.ne
    frgrncvvdeq.xy
    frgrncvvdeq.f
    frgrncvvdeq.a
    frgrncvvdeqlem3
    eqtrd
end
