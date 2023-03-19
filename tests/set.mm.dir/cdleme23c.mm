include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "atbase.mm"
include "simp13l.mm"
include "latlej1.mm"
include "syl3anc.mm"
include "simp2l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "simp32.mm"
include "simp33.mm"
include "eqtr4d.mm"
include "breqtrd.mm"
include "wb.mm"
include "hlatjcl.mm"
include "latjcl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "oveq2i.mm"
include "latlej2.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "syl5eq.mm"
include "breqtrrd.mm"

theorem cdleme23c
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cX: class X
  assume cdleme23.b: |- B = ( Base ` K )
  assume cdleme23.l: |- .<_ = ( le ` K )
  assume cdleme23.j: |- .\/ = ( join ` K )
  assume cdleme23.m: |- ./\ = ( meet ` K )
  assume cdleme23.a: |- A = ( Atoms ` K )
  assume cdleme23.h: |- H = ( LHyp ` K )
  assume cdleme23.v: |- V = ( ( S .\/ T ) ./\ ( X ./\ W ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( X e. B /\ -. X .<_ W ) /\ ( S =/= T /\ ( S .\/ ( X ./\ W ) ) = X /\ ( T .\/ ( X ./\ W ) ) = X ) ) -> S .<_ ( T .\/ V ) )

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
    cT
    cA
    wcel
    #
    cT
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
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
    cS
    cT
    wne
    #
    cS
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    cT
    @14
    c.or
    co
    #
    cX
    wceq
    #
    w3a
    #
    w3a
    #
    cS
    cS
    cT
    c.or
    co
    #
    @17
    c.an
    co
    #
    cT
    cV
    c.or
    co
    #
    c.le
    @20
    cS
    @21
    c.le
    wbr
    #
    cS
    @17
    c.le
    wbr
    #
    cS
    @22
    c.le
    wbr
    #
    @20
    cK
    clat
    wcel
    #
    cS
    cB
    wcel
    #
    cT
    cB
    wcel
    #
    @24
    @20
    @0
    @27
    @0
    @1
    @5
    @8
    @12
    @19
    simp11l
    #
    cK
    hllat
    syl
    #
    @20
    @3
    @28
    @3
    @4
    @2
    @8
    @12
    @19
    simp12l
    #
    cA
    cB
    cS
    cK
    cdleme23.b
    cdleme23.a
    atbase
    syl
    #
    @20
    @6
    @29
    @6
    @7
    @2
    @5
    @12
    @19
    simp13l
    #
    cA
    cB
    cT
    cK
    cdleme23.b
    cdleme23.a
    atbase
    syl
    #
    cB
    c.or
    cK
    c.le
    cS
    cT
    cdleme23.b
    cdleme23.l
    cdleme23.j
    latlej1
    syl3anc
    @20
    cS
    @15
    @17
    c.le
    @20
    @27
    @28
    @14
    cB
    wcel
    #
    cS
    @15
    c.le
    wbr
    @31
    @33
    @20
    @27
    @10
    cW
    cB
    wcel
    #
    @36
    @31
    @9
    @10
    @11
    @19
    simp2l
    @20
    @1
    @37
    @0
    @1
    @5
    @8
    @12
    @19
    simp11r
    cB
    cH
    cK
    cW
    cdleme23.b
    cdleme23.h
    lhpbase
    syl
    cB
    cK
    c.an
    cX
    cW
    cdleme23.b
    cdleme23.m
    latmcl
    syl3anc
    #
    cB
    c.or
    cK
    c.le
    cS
    @14
    cdleme23.b
    cdleme23.l
    cdleme23.j
    latlej1
    syl3anc
    @20
    @15
    cX
    @17
    @9
    @12
    @13
    @16
    @18
    simp32
    @9
    @12
    @13
    @16
    @18
    simp33
    eqtr4d
    breqtrd
    @20
    @27
    @28
    @21
    cB
    wcel
    #
    @17
    cB
    wcel
    #
    @24
    @25
    wa
    @26
    wb
    @31
    @33
    @20
    @0
    @3
    @6
    @39
    @30
    @32
    @34
    cA
    cB
    c.or
    cK
    cS
    cT
    cdleme23.b
    cdleme23.j
    cdleme23.a
    hlatjcl
    syl3anc
    #
    @20
    @27
    @29
    @36
    @40
    @31
    @35
    @38
    cB
    c.or
    cK
    cT
    @14
    cdleme23.b
    cdleme23.j
    latjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    cS
    @21
    @17
    cdleme23.b
    cdleme23.l
    cdleme23.m
    latlem12
    syl13anc
    mpbi2and
    @20
    @23
    cT
    @21
    @14
    c.an
    co
    #
    c.or
    co
    #
    @22
    cV
    @42
    cT
    c.or
    cdleme23.v
    oveq2i
    @20
    @0
    @6
    @39
    @36
    cT
    @21
    c.le
    wbr
    #
    @43
    @22
    wceq
    @30
    @34
    @41
    @38
    @20
    @27
    @28
    @29
    @44
    @31
    @33
    @35
    cB
    c.or
    cK
    c.le
    cS
    cT
    cdleme23.b
    cdleme23.l
    cdleme23.j
    latlej2
    syl3anc
    cA
    cB
    cT
    c.or
    cK
    c.le
    c.an
    @21
    @14
    cdleme23.b
    cdleme23.l
    cdleme23.j
    cdleme23.m
    cdleme23.a
    atmod3i1
    syl131anc
    syl5eq
    breqtrrd
end
