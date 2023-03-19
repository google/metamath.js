include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "clat.mm"
include "wceq.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "atbase.mm"
include "simp3l.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "simp1.mm"
include "simp3r.mm"
include "lhpmod6i1.mm"
include "syl121anc.mm"
include "cp0.mm"
include "cfv.mm"
include "eqid.mm"
include "lhpmat.mm"
include "3adant3.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olj01.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "3eqtr2d.mm"

theorem lhple
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
  assume lhple.b: |- B = ( Base ` K )
  assume lhple.l: |- .<_ = ( le ` K )
  assume lhple.j: |- .\/ = ( join ` K )
  assume lhple.m: |- ./\ = ( meet ` K )
  assume lhple.a: |- A = ( Atoms ` K )
  assume lhple.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( X e. B /\ X .<_ W ) ) -> ( ( P .\/ X ) ./\ W ) = X )

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
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
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
    #
    wa
    #
    w3a
    #
    cP
    cX
    c.or
    co
    #
    cW
    c.an
    co
    cX
    cP
    c.or
    co
    #
    cW
    c.an
    co
    #
    cX
    cP
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    @9
    @10
    @11
    cW
    c.an
    @9
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @6
    @10
    @11
    wceq
    @9
    @0
    @15
    @0
    @1
    @5
    @8
    simp1l
    #
    cK
    hllat
    syl
    @9
    @3
    @16
    @2
    @3
    @4
    @8
    simp2l
    cA
    cB
    cP
    cK
    lhple.b
    lhple.a
    atbase
    syl
    #
    @2
    @5
    @6
    @7
    simp3l
    #
    cB
    c.or
    cK
    cP
    cX
    lhple.b
    lhple.j
    latjcom
    syl3anc
    oveq1d
    @9
    @2
    @6
    @16
    @7
    @14
    @12
    wceq
    @2
    @5
    @8
    simp1
    @19
    @18
    @2
    @5
    @6
    @7
    simp3r
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cP
    lhple.b
    lhple.l
    lhple.j
    lhple.m
    lhple.h
    lhpmod6i1
    syl121anc
    @9
    @14
    cX
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    cX
    @9
    @13
    @20
    cX
    c.or
    @2
    @5
    @13
    @20
    wceq
    @8
    cA
    cP
    cH
    cK
    c.le
    c.an
    cW
    @20
    lhple.l
    lhple.m
    @20
    eqid
    #
    lhple.a
    lhple.h
    lhpmat
    3adant3
    oveq2d
    @9
    cK
    col
    wcel
    #
    @6
    @21
    cX
    wceq
    @9
    @0
    @23
    @17
    cK
    hlol
    syl
    @19
    cB
    c.or
    cK
    cX
    @20
    lhple.b
    lhple.j
    @22
    olj01
    syl2anc
    eqtrd
    3eqtr2d
end
