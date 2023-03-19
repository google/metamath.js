include "crusgr.mm"
include "wbr.mm"
include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "c3.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "co.mm"
include "chash.mm"
include "c2.mm"
include "cmin.mm"
include "caddc.mm"
include "cexp.mm"
include "cclwwlknon.mm"
include "wceq.mm"
include "eluzelcn.mm"
include "2cnd.mm"
include "npcand.mm"
include "eqcomd.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "cn.mm"
include "simplr.mm"
include "simpr2.mm"
include "uz3m2nn.mm"
include "numclwwlk2lem3.mm"
include "syl3anc.mm"
include "simpl.mm"
include "simp1.mm"
include "anim12i.mm"
include "anim2i.mm"
include "3adant1.mm"
include "numclwwlkqhash.mm"
include "syl2anc.mm"
include "3eqtr2d.mm"

theorem numclwwlk2
  let vw: setvar w
  let vv: setvar v
  let cQ: class Q
  let vn: setvar n
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cX: class X
  let vf: setvar f
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
  disjoint K w
  disjoint V w
  disjoint G f
  disjoint f w
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
  assert |- ( ( ( G RegUSGraph K /\ G e. FriendGraph ) /\ ( V e. Fin /\ X e. V /\ N e. ( ZZ>= ` 3 ) ) ) -> ( # ` ( X H N ) ) = ( ( K ^ ( N - 2 ) ) - ( # ` ( X ( ClWWalksNOn ` G ) ( N - 2 ) ) ) ) )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cG
    cfrgr
    wcel
    #
    wa
    #
    cV
    cfn
    wcel
    #
    cX
    cV
    wcel
    #
    cN
    c3
    cuz
    cfv
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cN
    cH
    co
    #
    chash
    cfv
    cX
    cN
    c2
    cmin
    co
    #
    c2
    caddc
    co
    #
    cH
    co
    #
    chash
    cfv
    #
    cX
    @9
    cQ
    co
    chash
    cfv
    #
    cK
    @9
    cexp
    co
    cX
    @9
    cG
    cclwwlknon
    cfv
    co
    chash
    cfv
    cmin
    co
    #
    @7
    @8
    @11
    chash
    @7
    cN
    @10
    cX
    cH
    @6
    cN
    @10
    wceq
    #
    @2
    @5
    @3
    @15
    @4
    @5
    @10
    cN
    @5
    cN
    c2
    c3
    cN
    eluzelcn
    @5
    2cnd
    npcand
    eqcomd
    3ad2ant3
    adantl
    oveq2d
    fveq2d
    @7
    @1
    @4
    @9
    cn
    wcel
    #
    @13
    @12
    wceq
    @0
    @1
    @6
    simplr
    @2
    @3
    @4
    @5
    simpr2
    @6
    @16
    @2
    @5
    @3
    @16
    @4
    cN
    uz3m2nn
    #
    3ad2ant3
    adantl
    vw
    vv
    cQ
    vn
    cG
    cH
    @9
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlk.h
    numclwwlk2lem3
    syl3anc
    @7
    @0
    @3
    wa
    @4
    @16
    wa
    #
    @13
    @14
    wceq
    @2
    @0
    @6
    @3
    @0
    @1
    simpl
    @3
    @4
    @5
    simp1
    anim12i
    @6
    @18
    @2
    @4
    @5
    @18
    @3
    @5
    @16
    @4
    @17
    anim2i
    3adant1
    adantl
    vw
    vv
    cQ
    vn
    cG
    cK
    @9
    cV
    cX
    numclwwlk.v
    numclwwlk.q
    numclwwlkqhash
    syl2anc
    3eqtr2d
end
