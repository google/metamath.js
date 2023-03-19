include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "cv.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "oveq1.mm"
include "adantl.mm"
include "simpr.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "ex.mm"

theorem numclwlk2lem2fv
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let cQ: class Q
  let cR: class R
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let cK: class K
  let vi: setvar i
  assume numclwwlk.v: |- V = ( Vtx ` G )
  assume numclwwlk.q: |- Q = ( v e. V , n e. NN |-> { w e. ( n WWalksN G ) | ( ( w ` 0 ) = v /\ ( lastS ` w ) =/= v ) } )
  assume numclwwlk.h: |- H = ( v e. V , n e. NN |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) =/= ( w ` 0 ) ) } )
  assume numclwwlk.r: |- R = ( x e. ( X H ( N + 2 ) ) |-> ( x substr <. 0 , ( N + 1 ) >. ) )

  disjoint G w
  disjoint G x
  disjoint w x
  disjoint H x
  disjoint N x
  disjoint Q x
  disjoint V x
  disjoint X x
  disjoint W x
  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint V n
  disjoint V v
  disjoint X n
  disjoint X v
  disjoint X w
  disjoint V w
  disjoint W v
  disjoint W w
  disjoint G f
  disjoint f w
  disjoint K w
  disjoint N f
  disjoint V f
  disjoint X f
  disjoint G i
  disjoint N i
  disjoint W i
  assert |- ( ( X e. V /\ N e. NN ) -> ( W e. ( X H ( N + 2 ) ) -> ( R ` W ) = ( W substr <. 0 , ( N + 1 ) >. ) ) )

  proof
    cX
    cV
    wcel
    cN
    cn
    wcel
    wa
    #
    cW
    cX
    cN
    c2
    caddc
    co
    cH
    co
    #
    wcel
    #
    cW
    cR
    cfv
    cW
    cc0
    cN
    c1
    caddc
    co
    cop
    #
    csubstr
    co
    #
    wceq
    @0
    @2
    wa
    #
    vx
    cW
    vx
    cv
    #
    @3
    csubstr
    co
    #
    @4
    @1
    cR
    cvv
    cR
    vx
    @1
    @7
    cmpt
    wceq
    @5
    numclwwlk.r
    a1i
    @6
    cW
    wceq
    @7
    @4
    wceq
    @5
    @6
    cW
    @3
    csubstr
    oveq1
    adantl
    @0
    @2
    simpr
    @5
    cW
    @3
    csubstr
    ovexd
    fvmptd
    ex
end
