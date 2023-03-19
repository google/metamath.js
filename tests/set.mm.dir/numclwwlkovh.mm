include "cn.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "wne.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "crab.mm"
include "oveq1.mm"
include "adantl.mm"
include "eqeq2.mm"
include "fveq2d.mm"
include "neeq1d.mm"
include "bi2anan9.mm"
include "rabeqbidv.mm"
include "ovex.mm"
include "rabex.mm"
include "ovmpt2a.mm"

theorem numclwwlkovh
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
  assert |- ( ( X e. V /\ N e. NN ) -> ( X H N ) = { w e. ( N ClWWalksN G ) | ( ( w ` 0 ) = X /\ ( w ` ( N - 2 ) ) =/= ( w ` 0 ) ) } )

  proof
    vv
    vn
    cX
    cN
    cV
    cn
    cc0
    vw
    cv
    #
    cfv
    #
    vv
    cv
    #
    wceq
    #
    vn
    cv
    #
    c2
    cmin
    co
    #
    @0
    cfv
    #
    @1
    wne
    #
    wa
    #
    vw
    @4
    cG
    cclwwlkn
    co
    #
    crab
    @1
    cX
    wceq
    #
    cN
    c2
    cmin
    co
    #
    @0
    cfv
    #
    @1
    wne
    #
    wa
    #
    vw
    cN
    cG
    cclwwlkn
    co
    #
    crab
    cH
    @2
    cX
    wceq
    #
    @4
    cN
    wceq
    #
    wa
    @8
    @14
    vw
    @9
    @15
    @17
    @9
    @15
    wceq
    @16
    @4
    cN
    cG
    cclwwlkn
    oveq1
    adantl
    @16
    @3
    @10
    @17
    @7
    @13
    @2
    cX
    @1
    eqeq2
    @17
    @6
    @12
    @1
    @17
    @5
    @11
    @0
    @4
    cN
    c2
    cmin
    oveq1
    fveq2d
    neeq1d
    bi2anan9
    rabeqbidv
    numclwwlk.h
    @14
    vw
    @15
    cN
    cG
    cclwwlkn
    ovex
    rabex
    ovmpt2a
end
