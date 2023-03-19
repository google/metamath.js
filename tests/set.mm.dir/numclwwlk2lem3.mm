include "cfrgr.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "cc0.mm"
include "c1.mm"
include "cop.mm"
include "csubstr.mm"
include "cmpt.mm"
include "ovexd.mm"
include "eqid.mm"
include "numclwlk2lem2f1o.mm"
include "hasheqf1od.mm"
include "eqcomd.mm"

theorem numclwwlk2lem3
  let vw: setvar w
  let vv: setvar v
  let cQ: class Q
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cN: class N
  let cV: class V
  let cX: class X
  let vf: setvar f
  let cK: class K
  let vi: setvar i
  let cW: class W
  let vh: setvar h
  assume numclwwlk.v: |- V = ( Vtx ` G )
  assume numclwwlk.q: |- Q = ( v e. V , n e. NN |-> { w e. ( n WWalksN G ) | ( ( w ` 0 ) = v /\ ( lastS ` w ) =/= v ) } )
  assume numclwwlk.h: |- H = ( v e. V , n e. NN |-> { w e. ( n ClWWalksN G ) | ( ( w ` 0 ) = v /\ ( w ` ( n - 2 ) ) =/= ( w ` 0 ) ) } )

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
  disjoint G f
  disjoint f w
  disjoint K w
  disjoint N f
  disjoint V f
  disjoint X f
  disjoint G i
  disjoint N i
  disjoint W i
  disjoint W v
  disjoint W w
  disjoint G h
  disjoint h w
  disjoint H h
  disjoint N h
  disjoint Q h
  disjoint V h
  disjoint h v
  disjoint X h
  assert |- ( ( G e. FriendGraph /\ X e. V /\ N e. NN ) -> ( # ` ( X Q N ) ) = ( # ` ( X H ( N + 2 ) ) ) )

  proof
    cG
    cfrgr
    wcel
    cX
    cV
    wcel
    cN
    cn
    wcel
    w3a
    #
    cX
    cN
    c2
    caddc
    co
    #
    cH
    co
    #
    chash
    cfv
    cX
    cN
    cQ
    co
    #
    chash
    cfv
    @0
    @2
    @3
    cvv
    vh
    @2
    vh
    cv
    cc0
    cN
    c1
    caddc
    co
    cop
    csubstr
    co
    cmpt
    #
    @0
    cX
    @1
    cH
    ovexd
    vh
    vw
    vv
    cQ
    @4
    vn
    cG
    cH
    cN
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    @4
    eqid
    numclwlk2lem2f1o
    hasheqf1od
    eqcomd
end
