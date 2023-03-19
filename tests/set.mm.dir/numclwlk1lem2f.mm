include "cusgr.mm"
include "wcel.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "c1.mm"
include "cnbgr.mm"
include "cxp.mm"
include "cclwwlkn.mm"
include "wceq.mm"
include "wa.mm"
include "extwwlkfabel.mm"
include "simpr1.mm"
include "simpr2.mm"
include "opelxpd.mm"
include "syl6bi.mm"
include "imp.mm"
include "fmptd.mm"

theorem numclwlk1lem2f
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
  let vi: setvar i
  let cY: class Y
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )
  assume numclwwlk.t: |- T = ( u e. ( X C N ) |-> <. ( u substr <. 0 , ( N - 2 ) >. ) , ( u ` ( N - 1 ) ) >. )

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
  disjoint W w
  disjoint G i
  disjoint W i
  disjoint Y w
  assert |- ( ( G e. USGraph /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) -> T : ( X C N ) --> ( F X. ( G NeighbVtx X ) ) )

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
    #
    vu
    cX
    cN
    cC
    co
    #
    vu
    cv
    #
    cc0
    cN
    c2
    cmin
    co
    #
    cop
    csubstr
    co
    #
    cN
    c1
    cmin
    co
    @2
    cfv
    #
    cop
    #
    cF
    cG
    cX
    cnbgr
    co
    #
    cxp
    #
    cT
    @0
    @2
    @1
    wcel
    #
    @6
    @8
    wcel
    #
    @0
    @9
    @2
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    @4
    cF
    wcel
    #
    @5
    @7
    wcel
    #
    @3
    @2
    cfv
    cX
    wceq
    #
    w3a
    wa
    #
    @10
    vw
    vv
    cC
    vn
    cF
    cG
    cN
    cV
    @2
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    extwwlkfabel
    @15
    @4
    @5
    cF
    @7
    @11
    @12
    @13
    @14
    simpr1
    @11
    @12
    @13
    @14
    simpr2
    opelxpd
    syl6bi
    imp
    numclwwlk.t
    fmptd
end
