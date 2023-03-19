include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "w3a.mm"
include "simp2rr.mm"
include "simp33.mm"
include "clat.mm"
include "wb.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2rl.mm"
include "atbase.mm"
include "simp2ll.mm"
include "simp31.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "biimpd.mm"
include "mpand.mm"
include "simp32.mm"
include "wi.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "lattr.mm"
include "mpan2d.mm"
include "syld.mm"
include "mtod.mm"

theorem lhpmcvr4N
  let cA: class A
  let cB: class B
  let cP: class P
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume lhpmcvr2.b: |- B = ( Base ` K )
  assume lhpmcvr2.l: |- .<_ = ( le ` K )
  assume lhpmcvr2.j: |- .\/ = ( join ` K )
  assume lhpmcvr2.m: |- ./\ = ( meet ` K )
  assume lhpmcvr2.a: |- A = ( Atoms ` K )
  assume lhpmcvr2.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( X e. B /\ -. X .<_ W ) /\ ( P e. A /\ -. P .<_ W ) ) /\ ( Y e. B /\ ( X ./\ Y ) .<_ W /\ P .<_ X ) ) -> -. P .<_ Y )

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
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    cY
    cB
    wcel
    #
    cX
    cY
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    cP
    cX
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cP
    cY
    c.le
    wbr
    #
    @7
    @6
    @8
    @5
    @2
    @15
    simp2rr
    @16
    @17
    cP
    @12
    c.le
    wbr
    #
    @7
    @16
    @14
    @17
    @18
    @2
    @10
    @11
    @13
    @14
    simp33
    @16
    @14
    @17
    wa
    #
    @18
    @16
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @3
    @11
    @19
    @18
    wb
    @16
    @0
    @20
    @0
    @1
    @10
    @15
    simp1l
    cK
    hllat
    syl
    #
    @16
    @6
    @21
    @6
    @8
    @5
    @2
    @15
    simp2rl
    cA
    cB
    cP
    cK
    lhpmcvr2.b
    lhpmcvr2.a
    atbase
    syl
    #
    @3
    @4
    @9
    @2
    @15
    simp2ll
    #
    @2
    @10
    @11
    @13
    @14
    simp31
    #
    cB
    cK
    c.le
    c.an
    cP
    cX
    cY
    lhpmcvr2.b
    lhpmcvr2.l
    lhpmcvr2.m
    latlem12
    syl13anc
    biimpd
    mpand
    @16
    @18
    @13
    @7
    @2
    @10
    @11
    @13
    @14
    simp32
    @16
    @20
    @21
    @12
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @18
    @13
    wa
    @7
    wi
    @22
    @23
    @16
    @20
    @3
    @11
    @26
    @22
    @24
    @25
    cB
    cK
    c.an
    cX
    cY
    lhpmcvr2.b
    lhpmcvr2.m
    latmcl
    syl3anc
    @16
    @1
    @27
    @0
    @1
    @10
    @15
    simp1r
    cB
    cH
    cK
    cW
    lhpmcvr2.b
    lhpmcvr2.h
    lhpbase
    syl
    cB
    cK
    c.le
    cP
    @12
    cW
    lhpmcvr2.b
    lhpmcvr2.l
    lattr
    syl13anc
    mpan2d
    syld
    mtod
end
