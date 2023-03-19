include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "wn.mm"
include "wrex.mm"
include "co.mm"
include "hlrelat1.mm"
include "imp.mm"
include "simp3l.mm"
include "wb.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp2.mm"
include "cvr1.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simp1l.mm"
include "simp1r.mm"
include "pltle.mm"
include "sylc.mm"
include "simp3r.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "simp1l3.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "jca.mm"
include "3exp.mm"
include "reximdvai.mm"
include "mpd.mm"

theorem hlrelat3
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume hlrelat3.b: |- B = ( Base ` K )
  assume hlrelat3.l: |- .<_ = ( le ` K )
  assume hlrelat3.s: |- .< = ( lt ` K )
  assume hlrelat3.j: |- .\/ = ( join ` K )
  assume hlrelat3.c: |- C = ( <o ` K )
  assume hlrelat3.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint .< p
  disjoint X p
  disjoint Y p
  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ X .< Y ) -> E. p e. A ( X C ( X .\/ p ) /\ ( X .\/ p ) .<_ Y ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.lt
    wbr
    #
    wa
    #
    vp
    cv
    #
    cX
    c.le
    wbr
    wn
    #
    @6
    cY
    c.le
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    #
    cX
    cX
    @6
    c.or
    co
    #
    cC
    wbr
    #
    @11
    cY
    c.le
    wbr
    #
    wa
    #
    vp
    cA
    wrex
    @3
    @4
    @10
    cA
    cB
    c.lt
    cK
    c.le
    cX
    cY
    vp
    hlrelat3.b
    hlrelat3.l
    hlrelat3.s
    hlrelat3.a
    hlrelat1
    imp
    @5
    @9
    @14
    vp
    cA
    @5
    @6
    cA
    wcel
    #
    @9
    @14
    @5
    @15
    @9
    w3a
    #
    @12
    @13
    @16
    @7
    @12
    @5
    @15
    @7
    @8
    simp3l
    @16
    @0
    @1
    @15
    @7
    @12
    wb
    @0
    @1
    @2
    @4
    @15
    @9
    simp1l1
    #
    @0
    @1
    @2
    @4
    @15
    @9
    simp1l2
    #
    @5
    @15
    @9
    simp2
    #
    cA
    cB
    cC
    @6
    c.or
    cK
    c.le
    cX
    hlrelat3.b
    hlrelat3.l
    hlrelat3.j
    hlrelat3.c
    hlrelat3.a
    cvr1
    syl3anc
    mpbid
    @16
    cX
    cY
    c.le
    wbr
    #
    @8
    @13
    @16
    @3
    @4
    @20
    @3
    @4
    @15
    @9
    simp1l
    @3
    @4
    @15
    @9
    simp1r
    chlt
    cB
    cB
    c.lt
    cK
    c.le
    cX
    cY
    hlrelat3.l
    hlrelat3.s
    pltle
    sylc
    @5
    @15
    @7
    @8
    simp3r
    @16
    cK
    clat
    wcel
    #
    @1
    @6
    cB
    wcel
    #
    @2
    @20
    @8
    wa
    @13
    wb
    @16
    @0
    @21
    @17
    cK
    hllat
    syl
    @18
    @16
    @15
    @22
    @19
    cA
    cB
    @6
    cK
    hlrelat3.b
    hlrelat3.a
    atbase
    syl
    @0
    @1
    @2
    @4
    @15
    @9
    simp1l3
    cB
    c.or
    cK
    c.le
    cX
    @6
    cY
    hlrelat3.b
    hlrelat3.l
    hlrelat3.j
    latjle12
    syl13anc
    mpbi2and
    jca
    3exp
    reximdvai
    mpd
end
