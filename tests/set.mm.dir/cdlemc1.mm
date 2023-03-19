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
include "simp3l.mm"
include "atbase.mm"
include "simp2.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcom.mm"
include "latlej1.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "cp1.mm"
include "cfv.mm"
include "eqid.mm"
include "lhpjat1.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem cdlemc1
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
  assume cdlemc1.b: |- B = ( Base ` K )
  assume cdlemc1.l: |- .<_ = ( le ` K )
  assume cdlemc1.j: |- .\/ = ( join ` K )
  assume cdlemc1.m: |- ./\ = ( meet ` K )
  assume cdlemc1.a: |- A = ( Atoms ` K )
  assume cdlemc1.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ ( P e. A /\ -. P .<_ W ) ) -> ( P .\/ ( ( P .\/ X ) ./\ W ) ) = ( P .\/ X ) )

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
    w3a
    #
    cP
    cP
    cX
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
    @9
    cP
    c.or
    co
    #
    @8
    cW
    cP
    c.or
    co
    #
    c.an
    co
    #
    @8
    @7
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @9
    cB
    wcel
    #
    @10
    @11
    wceq
    @7
    @0
    @14
    @0
    @1
    @3
    @6
    simp1l
    #
    cK
    hllat
    syl
    #
    @7
    @4
    @15
    @2
    @3
    @4
    @5
    simp3l
    #
    cA
    cB
    cP
    cK
    cdlemc1.b
    cdlemc1.a
    atbase
    syl
    #
    @7
    @14
    @8
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @16
    @18
    @7
    @14
    @15
    @3
    @21
    @18
    @20
    @2
    @3
    @6
    simp2
    #
    cB
    c.or
    cK
    cP
    cX
    cdlemc1.b
    cdlemc1.j
    latjcl
    syl3anc
    #
    @7
    @1
    @22
    @0
    @1
    @3
    @6
    simp1r
    cB
    cH
    cK
    cW
    cdlemc1.b
    cdlemc1.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    @8
    cW
    cdlemc1.b
    cdlemc1.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    cP
    @9
    cdlemc1.b
    cdlemc1.j
    latjcom
    syl3anc
    @7
    @0
    @4
    @21
    @22
    cP
    @8
    c.le
    wbr
    #
    @11
    @13
    wceq
    @17
    @19
    @24
    @25
    @7
    @14
    @15
    @3
    @26
    @18
    @20
    @23
    cB
    c.or
    cK
    c.le
    cP
    cX
    cdlemc1.b
    cdlemc1.l
    cdlemc1.j
    latlej1
    syl3anc
    cA
    cB
    cP
    c.or
    cK
    c.le
    c.an
    @8
    cW
    cdlemc1.b
    cdlemc1.l
    cdlemc1.j
    cdlemc1.m
    cdlemc1.a
    atmod2i1
    syl131anc
    @7
    @13
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
    @12
    @27
    @8
    c.an
    @2
    @6
    @12
    @27
    wceq
    @3
    cA
    cP
    @27
    cH
    c.or
    cK
    c.le
    cW
    cdlemc1.l
    cdlemc1.j
    @27
    eqid
    #
    cdlemc1.a
    cdlemc1.h
    lhpjat1
    3adant2
    oveq2d
    @7
    cK
    col
    wcel
    #
    @21
    @28
    @8
    wceq
    @7
    @0
    @30
    @17
    cK
    hlol
    syl
    @24
    cB
    @27
    cK
    c.an
    @8
    cdlemc1.b
    cdlemc1.m
    @29
    olm11
    syl2anc
    eqtrd
    3eqtrd
end
