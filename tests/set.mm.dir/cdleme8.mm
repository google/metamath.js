include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "oveq2i.mm"
include "cp1.mm"
include "cfv.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp2l.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "3ad2ant3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latlej1.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "lhpjat2.mm"
include "3adant3.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem cdleme8
  let cA: class A
  let cC: class C
  let cP: class P
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme8.l: |- .<_ = ( le ` K )
  assume cdleme8.j: |- .\/ = ( join ` K )
  assume cdleme8.m: |- ./\ = ( meet ` K )
  assume cdleme8.a: |- A = ( Atoms ` K )
  assume cdleme8.h: |- H = ( LHyp ` K )
  assume cdleme8.4: |- C = ( ( P .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ S e. A ) -> ( P .\/ C ) = ( P .\/ S ) )

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
    cS
    cA
    wcel
    #
    w3a
    #
    cP
    cC
    c.or
    co
    cP
    cP
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    @8
    cC
    @9
    cP
    c.or
    cdleme8.4
    oveq2i
    @7
    @10
    @8
    cP
    cW
    c.or
    co
    #
    c.an
    co
    #
    @8
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @8
    @7
    @0
    @3
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @15
    wcel
    #
    cP
    @8
    c.le
    wbr
    #
    @10
    @12
    wceq
    @0
    @1
    @5
    @6
    simp1l
    #
    @2
    @3
    @4
    @6
    simp2l
    #
    @7
    cK
    clat
    wcel
    #
    cP
    @15
    wcel
    #
    cS
    @15
    wcel
    #
    @16
    @7
    @0
    @21
    @19
    cK
    hllat
    syl
    #
    @7
    @3
    @22
    @20
    cA
    @15
    cP
    cK
    @15
    eqid
    #
    cdleme8.a
    atbase
    syl
    #
    @6
    @2
    @23
    @5
    cA
    @15
    cS
    cK
    @25
    cdleme8.a
    atbase
    3ad2ant3
    #
    @15
    c.or
    cK
    cP
    cS
    @25
    cdleme8.j
    latjcl
    syl3anc
    #
    @7
    @1
    @17
    @0
    @1
    @5
    @6
    simp1r
    @15
    cH
    cK
    cW
    @25
    cdleme8.h
    lhpbase
    syl
    @7
    @21
    @22
    @23
    @18
    @24
    @26
    @27
    @15
    c.or
    cK
    c.le
    cP
    cS
    @25
    cdleme8.l
    cdleme8.j
    latlej1
    syl3anc
    cA
    @15
    cP
    c.or
    cK
    c.le
    c.an
    @8
    cW
    @25
    cdleme8.l
    cdleme8.j
    cdleme8.m
    cdleme8.a
    atmod3i1
    syl131anc
    @7
    @11
    @13
    @8
    c.an
    @2
    @5
    @11
    @13
    wceq
    @6
    cA
    cP
    @13
    cH
    c.or
    cK
    c.le
    cW
    cdleme8.l
    cdleme8.j
    @13
    eqid
    #
    cdleme8.a
    cdleme8.h
    lhpjat2
    3adant3
    oveq2d
    @7
    cK
    col
    wcel
    #
    @16
    @14
    @8
    wceq
    @7
    @0
    @30
    @19
    cK
    hlol
    syl
    @28
    @15
    @13
    cK
    c.an
    @8
    @25
    cdleme8.m
    @29
    olm11
    syl2anc
    3eqtrd
    syl5eq
end
