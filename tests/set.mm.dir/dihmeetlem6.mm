include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "simprlr.mm"
include "clat.mm"
include "wb.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simprll.mm"
include "atbase.mm"
include "simpl1r.mm"
include "lhpbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "simpr.mm"
include "syl6bir.mm"
include "mtod.mm"
include "wceq.mm"
include "simprr.mm"
include "dihmeetlem5.mm"
include "syl32anc.mm"
include "breq1d.mm"
include "mtbird.mm"

theorem dihmeetlem6
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihmeetlem6.b: |- B = ( Base ` K )
  assume dihmeetlem6.l: |- .<_ = ( le ` K )
  assume dihmeetlem6.h: |- H = ( LHyp ` K )
  assume dihmeetlem6.j: |- .\/ = ( join ` K )
  assume dihmeetlem6.m: |- ./\ = ( meet ` K )
  assume dihmeetlem6.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ Q .<_ X ) ) -> -. ( X ./\ ( Y .\/ Q ) ) .<_ W )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
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
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cQ
    cX
    c.le
    wbr
    #
    wa
    #
    wa
    #
    cX
    cY
    cQ
    c.or
    co
    c.an
    co
    #
    cW
    c.le
    wbr
    cX
    cY
    c.an
    co
    #
    cQ
    c.or
    co
    #
    cW
    c.le
    wbr
    #
    @12
    @16
    @7
    @5
    @6
    @8
    @10
    simprlr
    @12
    @16
    @14
    cW
    c.le
    wbr
    #
    @7
    wa
    #
    @7
    @12
    cK
    clat
    wcel
    #
    @14
    cB
    wcel
    #
    cQ
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @18
    @16
    wb
    @12
    @0
    @19
    @0
    @1
    @3
    @4
    @11
    simpl1l
    #
    cK
    hllat
    syl
    #
    @12
    @19
    @3
    @4
    @20
    @24
    @2
    @3
    @4
    @11
    simpl2
    #
    @2
    @3
    @4
    @11
    simpl3
    #
    cB
    cK
    c.an
    cX
    cY
    dihmeetlem6.b
    dihmeetlem6.m
    latmcl
    syl3anc
    @12
    @6
    @21
    @5
    @6
    @8
    @10
    simprll
    #
    cA
    cB
    cQ
    cK
    dihmeetlem6.b
    dihmeetlem6.a
    atbase
    syl
    @12
    @1
    @22
    @0
    @1
    @3
    @4
    @11
    simpl1r
    cB
    cH
    cK
    cW
    dihmeetlem6.b
    dihmeetlem6.h
    lhpbase
    syl
    cB
    c.or
    cK
    c.le
    @14
    cQ
    cW
    dihmeetlem6.b
    dihmeetlem6.l
    dihmeetlem6.j
    latjle12
    syl13anc
    @17
    @7
    simpr
    syl6bir
    mtod
    @12
    @13
    @15
    cW
    c.le
    @12
    @0
    @3
    @4
    @6
    @10
    @13
    @15
    wceq
    @23
    @25
    @26
    @27
    @5
    @9
    @10
    simprr
    cA
    cB
    cQ
    c.or
    cK
    c.le
    c.an
    cX
    cY
    dihmeetlem6.b
    dihmeetlem6.l
    dihmeetlem6.j
    dihmeetlem6.m
    dihmeetlem6.a
    dihmeetlem5
    syl32anc
    breq1d
    mtbird
end
