include "cv.mm"
include "cc0.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "cop.mm"
include "csubstr.mm"
include "c1.mm"
include "cfv.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq1.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"

theorem numclwlk1lem2fv
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
  let cW: class W
  let cX: class X
  let vi: setvar i
  let cY: class Y
  assume extwwlkfab.v: |- V = ( Vtx ` G )
  assume extwwlkfab.c: |- C = ( v e. V , n e. ( ZZ>= ` 2 ) |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) = ( w ` 0 ) ) } )
  assume extwwlkfab.f: |- F = ( X ( ClWWalksNOn ` G ) ( N - 2 ) )
  assume numclwwlk.t: |- T = ( u e. ( X C N ) |-> <. ( u substr <. 0 , ( N - 2 ) >. ) , ( u ` ( N - 1 ) ) >. )

  disjoint W u
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
  disjoint W w
  disjoint C u
  disjoint F u
  disjoint G u
  disjoint u w
  disjoint N u
  disjoint V u
  disjoint X u
  disjoint G i
  disjoint W i
  disjoint Y w
  assert |- ( W e. ( X C N ) -> ( T ` W ) = <. ( W substr <. 0 , ( N - 2 ) >. ) , ( W ` ( N - 1 ) ) >. )

  proof
    vu
    cW
    vu
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
    @0
    cfv
    #
    cop
    cW
    @1
    csubstr
    co
    #
    @3
    cW
    cfv
    #
    cop
    cX
    cN
    cC
    co
    cT
    @0
    cW
    wceq
    @2
    @5
    @4
    @6
    @0
    cW
    @1
    csubstr
    oveq1
    @3
    @0
    cW
    fveq1
    opeq12d
    numclwwlk.t
    @5
    @6
    opex
    fvmpt
end
