include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "csn.mm"
include "cnbgr.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "frgrncvvdeqlem5.mm"
include "wi.mm"
include "fvex.mm"
include "snid.mm"
include "eleq2.mm"
include "biimpa.mm"
include "elin.mm"
include "wnel.mm"
include "frgrncvvdeqlem1.mm"
include "wn.mm"
include "df-nel.mm"
include "nelelne.mm"
include "sylbi.mm"
include "syl.mm"
include "adantr.mm"
include "com12.mm"
include "simplbiim.mm"
include "mpan2.mm"
include "mpcom.mm"
include "ralrimiva.mm"

theorem frgrncvvdeqlem7
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
  assert |- ( ph -> A. x e. D ( A ` x ) =/= X )

  proof
    wph
    vx
    cv
    #
    cA
    cfv
    #
    cX
    wne
    #
    vx
    cD
    @1
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
    #
    wph
    @0
    cD
    wcel
    #
    wa
    #
    @2
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
    @1
    @3
    wcel
    #
    @8
    @2
    wi
    #
    @1
    @0
    cA
    fvex
    snid
    @6
    @9
    wa
    @1
    @5
    wcel
    #
    @10
    @6
    @9
    @11
    @3
    @5
    @1
    eleq2
    biimpa
    @11
    @1
    @4
    wcel
    @1
    cN
    wcel
    #
    @10
    @1
    @4
    cN
    elin
    @8
    @12
    @2
    wph
    @12
    @2
    wi
    #
    @7
    wph
    cX
    cN
    wnel
    #
    @13
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
    frgrncvvdeqlem1
    @14
    cX
    cN
    wcel
    wn
    @13
    cX
    cN
    df-nel
    cX
    cN
    @1
    nelelne
    sylbi
    syl
    adantr
    com12
    simplbiim
    syl
    mpan2
    mpcom
    ralrimiva
end
