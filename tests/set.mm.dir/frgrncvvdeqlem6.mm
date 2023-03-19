include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "cnbgr.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "frgrncvvdeqlem5.mm"
include "wi.mm"
include "cvv.mm"
include "fvex.mm"
include "elinsn.mm"
include "mpan.mm"
include "cfrgr.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "nbusgreledg.mm"
include "prcom.mm"
include "eleq1i.mm"
include "syl6bb.mm"
include "biimpd.mm"
include "3syl.mm"
include "adantr.mm"
include "com12.mm"
include "syl.mm"
include "eqcoms.mm"
include "mpcom.mm"

theorem frgrncvvdeqlem6
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
  assert |- ( ( ph /\ x e. D ) -> { x , ( A ` x ) } e. E )

  proof
    vx
    cv
    #
    cA
    cfv
    #
    csn
    #
    cG
    @0
    cnbgr
    co
    #
    cN
    cin
    #
    wceq
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @0
    @1
    cpr
    #
    cE
    wcel
    #
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
    frgrncvvdeqlem5
    @6
    @8
    wi
    #
    @4
    @2
    @4
    @2
    wceq
    #
    @1
    @3
    wcel
    #
    @1
    cN
    wcel
    #
    wa
    #
    @9
    @1
    cvv
    wcel
    @10
    @13
    @0
    cA
    fvex
    @1
    @3
    cN
    cvv
    elinsn
    mpan
    @11
    @9
    @12
    @6
    @11
    @8
    wph
    @11
    @8
    wi
    #
    @5
    wph
    cG
    cfrgr
    wcel
    cG
    cusgr
    wcel
    #
    @14
    frgrncvvdeq.f
    cG
    frgrusgr
    @15
    @11
    @8
    @15
    @11
    @1
    @0
    cpr
    #
    cE
    wcel
    @8
    cE
    cG
    @0
    @1
    frgrncvvdeq.e
    nbusgreledg
    @16
    @7
    cE
    @1
    @0
    prcom
    eleq1i
    syl6bb
    biimpd
    3syl
    adantr
    com12
    adantr
    syl
    eqcoms
    mpcom
end
