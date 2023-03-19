include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cfv.mm"
include "clat.mm"
include "wceq.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "atbase.mm"
include "simp12.mm"
include "simp13.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latjcom.mm"
include "fveq2d.mm"
include "dihjatc1.mm"
include "eqtrd.mm"

theorem dihjatc2N
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( Q .<_ X /\ ( X ./\ Y ) .<_ W ) ) -> ( I ` ( Q .\/ ( X ./\ Y ) ) ) = ( ( I ` Q ) .(+) ( I ` ( X ./\ Y ) ) ) )

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
    cQ
    @9
    c.or
    co
    #
    cI
    cfv
    @9
    cQ
    c.or
    co
    #
    cI
    cfv
    cQ
    cI
    cfv
    @9
    cI
    cfv
    c.po
    co
    @11
    @12
    @13
    cI
    @11
    cK
    clat
    wcel
    #
    cQ
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @12
    @13
    wceq
    @11
    @0
    @14
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
    #
    @11
    @6
    @15
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
    @11
    @14
    @3
    @4
    @16
    @17
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
    c.or
    cK
    cQ
    @9
    dihjatc1.b
    dihjatc1.j
    latjcom
    syl3anc
    fveq2d
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
    eqtrd
end
