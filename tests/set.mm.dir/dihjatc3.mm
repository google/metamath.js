include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cfv.mm"
include "dihjatc1.mm"
include "cabl.mm"
include "csubg.mm"
include "wceq.mm"
include "clmod.mm"
include "simp11.mm"
include "dvhlmod.mm"
include "lmodabl.mm"
include "syl.mm"
include "clss.mm"
include "wss.mm"
include "eqid.mm"
include "lsssssubg.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "simp12.mm"
include "simp13.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "dihlss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "simp2l.mm"
include "atbase.mm"
include "lsmcom.mm"
include "eqtr4d.mm"

theorem dihjatc3
  let cA: class A
  let cB: class B
  let c.po: class .(+)
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  assume dihjatc1.b: |- B = ( Base ` K )
  assume dihjatc1.l: |- .<_ = ( le ` K )
  assume dihjatc1.h: |- H = ( LHyp ` K )
  assume dihjatc1.j: |- .\/ = ( join ` K )
  assume dihjatc1.m: |- ./\ = ( meet ` K )
  assume dihjatc1.a: |- A = ( Atoms ` K )
  assume dihjatc1.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihjatc1.s: |- .(+) = ( LSSum ` U )
  assume dihjatc1.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( Q .<_ X /\ ( X ./\ Y ) .<_ W ) ) -> ( I ` ( ( X ./\ Y ) .\/ Q ) ) = ( ( I ` ( X ./\ Y ) ) .(+) ( I ` Q ) ) )

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
    wn
    #
    wa
    #
    cQ
    cX
    c.le
    wbr
    cX
    cY
    c.an
    co
    #
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    @9
    cQ
    c.or
    co
    cI
    cfv
    cQ
    cI
    cfv
    #
    @9
    cI
    cfv
    #
    c.po
    co
    #
    @13
    @12
    c.po
    co
    #
    cA
    cB
    c.po
    cQ
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cY
    dihjatc1.b
    dihjatc1.l
    dihjatc1.h
    dihjatc1.j
    dihjatc1.m
    dihjatc1.a
    dihjatc1.u
    dihjatc1.s
    dihjatc1.i
    dihjatc1
    @11
    cU
    cabl
    wcel
    #
    @13
    cU
    csubg
    cfv
    #
    wcel
    @12
    @17
    wcel
    @15
    @14
    wceq
    @11
    cU
    clmod
    wcel
    #
    @16
    @11
    cU
    cH
    cK
    cW
    dihjatc1.h
    dihjatc1.u
    @2
    @3
    @4
    @8
    @10
    simp11
    #
    dvhlmod
    #
    cU
    lmodabl
    syl
    @11
    cU
    clss
    cfv
    #
    @17
    @13
    @11
    @18
    @21
    @17
    wss
    @20
    @21
    cU
    @21
    eqid
    #
    lsssssubg
    syl
    #
    @11
    @2
    @9
    cB
    wcel
    #
    @13
    @21
    wcel
    @19
    @11
    cK
    clat
    wcel
    #
    @3
    @4
    @24
    @11
    @0
    @25
    @0
    @1
    @3
    @4
    @8
    @10
    simp11l
    cK
    hllat
    syl
    @2
    @3
    @4
    @8
    @10
    simp12
    @2
    @3
    @4
    @8
    @10
    simp13
    cB
    cK
    c.an
    cX
    cY
    dihjatc1.b
    dihjatc1.m
    latmcl
    syl3anc
    cB
    @21
    cU
    cH
    cI
    cK
    cW
    @9
    dihjatc1.b
    dihjatc1.h
    dihjatc1.i
    dihjatc1.u
    @22
    dihlss
    syl2anc
    sseldd
    @11
    @21
    @17
    @12
    @23
    @11
    @2
    cQ
    cB
    wcel
    #
    @12
    @21
    wcel
    @19
    @11
    @6
    @26
    @5
    @6
    @7
    @10
    simp2l
    cA
    cB
    cQ
    cK
    dihjatc1.b
    dihjatc1.a
    atbase
    syl
    cB
    @21
    cU
    cH
    cI
    cK
    cW
    cQ
    dihjatc1.b
    dihjatc1.h
    dihjatc1.i
    dihjatc1.u
    @22
    dihlss
    syl2anc
    sseldd
    c.po
    @13
    @12
    cU
    dihjatc1.s
    lsmcom
    syl3anc
    eqtr4d
end
