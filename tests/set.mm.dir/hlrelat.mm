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
include "clat.mm"
include "wb.mm"
include "simpll1.mm"
include "hllat.mm"
include "syl.mm"
include "simpll2.mm"
include "atbase.mm"
include "adantl.mm"
include "latnle.mm"
include "syl3anc.mm"
include "pltle.mm"
include "adantr.mm"
include "biantrurd.mm"
include "simpll3.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "rexbidva.mm"
include "mpbid.mm"

theorem hlrelat
  let cA: class A
  let cB: class B
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume hlrelat5.b: |- B = ( Base ` K )
  assume hlrelat5.l: |- .<_ = ( le ` K )
  assume hlrelat5.s: |- .< = ( lt ` K )
  assume hlrelat5.j: |- .\/ = ( join ` K )
  assume hlrelat5.a: |- A = ( Atoms ` K )

  disjoint A p
  disjoint B p
  disjoint K p
  disjoint .<_ p
  disjoint X p
  disjoint Y p
  disjoint .< p
  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ X .< Y ) -> E. p e. A ( X .< ( X .\/ p ) /\ ( X .\/ p ) .<_ Y ) )

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
    c.lt
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
    hlrelat5.b
    hlrelat5.l
    hlrelat5.s
    hlrelat5.a
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
    wa
    #
    @7
    @12
    @8
    @13
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
    @7
    @12
    wb
    @16
    @0
    @17
    @0
    @1
    @2
    @4
    @15
    simpll1
    cK
    hllat
    syl
    #
    @0
    @1
    @2
    @4
    @15
    simpll2
    #
    @15
    @18
    @5
    cA
    cB
    @6
    cK
    hlrelat5.b
    hlrelat5.a
    atbase
    adantl
    #
    cB
    c.lt
    c.or
    cK
    c.le
    cX
    @6
    hlrelat5.b
    hlrelat5.l
    hlrelat5.s
    hlrelat5.j
    latnle
    syl3anc
    @16
    @8
    cX
    cY
    c.le
    wbr
    #
    @8
    wa
    #
    @13
    @16
    @22
    @8
    @5
    @22
    @15
    @3
    @4
    @22
    chlt
    cB
    cB
    c.lt
    cK
    c.le
    cX
    cY
    hlrelat5.l
    hlrelat5.s
    pltle
    imp
    adantr
    biantrurd
    @16
    @17
    @1
    @18
    @2
    @23
    @13
    wb
    @19
    @20
    @21
    @0
    @1
    @2
    @4
    @15
    simpll3
    cB
    c.or
    cK
    c.le
    cX
    @6
    cY
    hlrelat5.b
    hlrelat5.l
    hlrelat5.j
    latjle12
    syl13anc
    bitrd
    anbi12d
    rexbidva
    mpbid
end
