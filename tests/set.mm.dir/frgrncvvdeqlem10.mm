include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "frgrncvvdeqlem8.mm"
include "frgrncvvdeqlem9.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem frgrncvvdeqlem10
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
  let vu: setvar u
  let vw: setvar w
  let vm: setvar m
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
  disjoint D y
  disjoint E x
  disjoint D n
  disjoint E n
  disjoint n y
  disjoint G n
  disjoint N n
  disjoint V n
  disjoint Y n
  disjoint n ph
  disjoint n x
  disjoint A u
  disjoint A w
  disjoint u w
  disjoint D u
  disjoint D w
  disjoint u y
  disjoint w y
  disjoint E u
  disjoint E w
  disjoint u x
  disjoint w x
  disjoint N u
  disjoint N w
  disjoint ph u
  disjoint ph w
  disjoint A m
  disjoint A n
  disjoint m n
  disjoint D m
  disjoint m x
  disjoint E m
  disjoint G m
  disjoint m y
  disjoint N m
  disjoint V m
  disjoint X m
  disjoint X n
  disjoint m ph
  assert |- ( ph -> A : D -1-1-onto-> N )

  proof
    wph
    cD
    cN
    cA
    wf1
    cD
    cN
    cA
    wfo
    cD
    cN
    cA
    wf1o
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
    frgrncvvdeqlem8
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
    frgrncvvdeqlem9
    cD
    cN
    cA
    df-f1o
    sylanbrc
end
