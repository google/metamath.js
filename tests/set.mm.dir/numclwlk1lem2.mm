include "co.mm"
include "cv.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "cop.mm"
include "csubstr.mm"
include "c1.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "cusgr.mm"
include "c3.mm"
include "cuz.mm"
include "w3a.mm"
include "cnbgr.mm"
include "cxp.mm"
include "wf1o.mm"
include "wex.mm"
include "ovex.mm"
include "mptex.mm"
include "weq.mm"
include "oveq1.mm"
include "fveq1.mm"
include "opeq12d.mm"
include "cbvmptv.mm"
include "numclwlk1lem2f1o.mm"
include "f1oeq1.mm"
include "spcegv.mm"
include "mpsyl.mm"

theorem numclwlk1lem2
  let vw: setvar w
  let vv: setvar v
  let cC: class C
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cW: class W
  let vi: setvar i
  let cY: class Y
  let vu: setvar u
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )

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
  disjoint C f
  disjoint C w
  disjoint f w
  disjoint F f
  disjoint G f
  disjoint N f
  disjoint X f
  disjoint W w
  disjoint G i
  disjoint W i
  disjoint Y w
  disjoint C u
  disjoint F u
  disjoint G u
  disjoint u w
  disjoint N u
  disjoint V u
  disjoint X u
  assert |- ( ( G e. USGraph /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) -> E. f f : ( X C N ) -1-1-onto-> ( F X. ( G NeighbVtx X ) ) )

  proof
    vw
    cX
    cN
    cC
    co
    #
    vw
    cv
    #
    cc0
    cN
    c2
    cmin
    co
    cop
    #
    csubstr
    co
    #
    cN
    c1
    cmin
    co
    #
    @1
    cfv
    #
    cop
    #
    cmpt
    #
    cvv
    wcel
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
    @0
    cF
    cG
    cX
    cnbgr
    co
    cxp
    #
    @7
    wf1o
    #
    @0
    @8
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    vw
    @0
    @6
    cX
    cN
    cC
    ovex
    mptex
    vw
    vv
    vu
    cC
    @7
    vn
    cF
    cG
    cN
    cV
    cX
    extwwlkfab.v
    extwwlkfab.c
    extwwlkfab.f
    vw
    vu
    @0
    @6
    vu
    cv
    #
    @2
    csubstr
    co
    #
    @4
    @12
    cfv
    #
    cop
    vw
    vu
    weq
    @3
    @13
    @5
    @14
    @1
    @12
    @2
    csubstr
    oveq1
    @4
    @1
    @12
    fveq1
    opeq12d
    cbvmptv
    numclwlk1lem2f1o
    @11
    @9
    vf
    @7
    cvv
    @0
    @8
    @10
    @7
    f1oeq1
    spcegv
    mpsyl
end
