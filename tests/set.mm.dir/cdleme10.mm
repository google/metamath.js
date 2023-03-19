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
include "simp3l.mm"
include "simp2.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "latlej2.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "latjcom.mm"
include "lhpjat2.mm"
include "3adant2.mm"
include "oveq12d.mm"
include "col.mm"
include "hlol.mm"
include "latjcl.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem cdleme10
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme10.l: |- .<_ = ( le ` K )
  assume cdleme10.j: |- .\/ = ( join ` K )
  assume cdleme10.m: |- ./\ = ( meet ` K )
  assume cdleme10.a: |- A = ( Atoms ` K )
  assume cdleme10.h: |- H = ( LHyp ` K )
  assume cdleme10.d: |- D = ( ( R .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ R e. A /\ ( S e. A /\ -. S .<_ W ) ) -> ( S .\/ D ) = ( S .\/ R ) )

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
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cS
    cD
    c.or
    co
    cS
    cR
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
    cS
    cR
    c.or
    co
    #
    cD
    @9
    cS
    c.or
    cdleme10.d
    oveq2i
    @7
    @10
    @8
    cS
    cW
    c.or
    co
    #
    c.an
    co
    #
    @11
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @11
    @7
    @0
    @4
    @8
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @16
    wcel
    #
    cS
    @8
    c.le
    wbr
    #
    @10
    @13
    wceq
    @0
    @1
    @3
    @6
    simp1l
    #
    @2
    @3
    @4
    @5
    simp3l
    #
    @7
    @0
    @3
    @4
    @17
    @20
    @2
    @3
    @6
    simp2
    @21
    cA
    @16
    c.or
    cK
    cR
    cS
    @16
    eqid
    #
    cdleme10.j
    cdleme10.a
    hlatjcl
    syl3anc
    @7
    @1
    @18
    @0
    @1
    @3
    @6
    simp1r
    @16
    cH
    cK
    cW
    @22
    cdleme10.h
    lhpbase
    syl
    @7
    cK
    clat
    wcel
    #
    cR
    @16
    wcel
    #
    cS
    @16
    wcel
    #
    @19
    @7
    @0
    @23
    @20
    cK
    hllat
    syl
    #
    @3
    @2
    @24
    @6
    cA
    @16
    cR
    cK
    @22
    cdleme10.a
    atbase
    3ad2ant2
    #
    @7
    @4
    @25
    @21
    cA
    @16
    cS
    cK
    @22
    cdleme10.a
    atbase
    syl
    #
    @16
    c.or
    cK
    c.le
    cR
    cS
    @22
    cdleme10.l
    cdleme10.j
    latlej2
    syl3anc
    cA
    @16
    cS
    c.or
    cK
    c.le
    c.an
    @8
    cW
    @22
    cdleme10.l
    cdleme10.j
    cdleme10.m
    cdleme10.a
    atmod3i1
    syl131anc
    @7
    @8
    @11
    @12
    @14
    c.an
    @7
    @23
    @24
    @25
    @8
    @11
    wceq
    @26
    @27
    @28
    @16
    c.or
    cK
    cR
    cS
    @22
    cdleme10.j
    latjcom
    syl3anc
    @2
    @6
    @12
    @14
    wceq
    @3
    cA
    cS
    @14
    cH
    c.or
    cK
    c.le
    cW
    cdleme10.l
    cdleme10.j
    @14
    eqid
    #
    cdleme10.a
    cdleme10.h
    lhpjat2
    3adant2
    oveq12d
    @7
    cK
    col
    wcel
    #
    @11
    @16
    wcel
    #
    @15
    @11
    wceq
    @7
    @0
    @30
    @20
    cK
    hlol
    syl
    @7
    @23
    @25
    @24
    @31
    @26
    @28
    @27
    @16
    c.or
    cK
    cS
    cR
    @22
    cdleme10.j
    latjcl
    syl3anc
    @16
    @14
    cK
    c.an
    @11
    @22
    cdleme10.m
    @29
    olm11
    syl2anc
    3eqtrd
    syl5eq
end
