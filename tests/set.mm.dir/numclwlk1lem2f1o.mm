include "cusgr.mm"
include "wcel.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "cnbgr.mm"
include "cxp.mm"
include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "numclwlk1lem2f1.mm"
include "numclwlk1lem2fo.mm"
include "df-f1o.mm"
include "sylanbrc.mm"

theorem numclwlk1lem2f1o
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cW: class W
  let va: setvar a
  let vp: setvar p
  let vb: setvar b
  let vx: setvar x
  let vi: setvar i
  let cY: class Y
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )
  assume numclwwlk.t: |- T = ( u e. ( X C N ) |-> <. ( u substr <. 0 , ( N - 2 ) >. ) , ( u ` ( N - 1 ) ) >. )

  disjoint C u
  disjoint G w
  disjoint T u
  disjoint V u
  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint F w
  disjoint C u
  disjoint F u
  disjoint G u
  disjoint u w
  disjoint N u
  disjoint V u
  disjoint X u
  disjoint W u
  disjoint C a
  disjoint C p
  disjoint a p
  disjoint a u
  disjoint p u
  disjoint G a
  disjoint G p
  disjoint a w
  disjoint p w
  disjoint N a
  disjoint N p
  disjoint T a
  disjoint T p
  disjoint V a
  disjoint V p
  disjoint X a
  disjoint X p
  disjoint C b
  disjoint C x
  disjoint a b
  disjoint a x
  disjoint b p
  disjoint b x
  disjoint p x
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F x
  disjoint G b
  disjoint G x
  disjoint b w
  disjoint w x
  disjoint N b
  disjoint N x
  disjoint T b
  disjoint T x
  disjoint V b
  disjoint V x
  disjoint X b
  disjoint X x
  disjoint a i
  disjoint b u
  disjoint W w
  disjoint G i
  disjoint W i
  disjoint Y w
  assert |- ( ( G e. USGraph /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) -> T : ( X C N ) -1-1-onto-> ( F X. ( G NeighbVtx X ) ) )

  proof
    cG
    cusgr
    wcel
    cX
    cV
    wcel
    cN
    c3
    cuz
    cfv
    wcel
    w3a
    cX
    cN
    cC
    co
    #
    cF
    cG
    cX
    cnbgr
    co
    cxp
    #
    cT
    wf1
    @0
    @1
    cT
    wfo
    @0
    @1
    cT
    wf1o
    vw
    vv
    vu
    cC
    cT
    vn
    cF
    cG
    cN
    cV
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    numclwwlk.t
    numclwlk1lem2f1
    vw
    vv
    vu
    cC
    cT
    vn
    cF
    cG
    cN
    cV
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    numclwwlk.t
    numclwlk1lem2fo
    @0
    @1
    cT
    df-f1o
    sylanbrc
end
