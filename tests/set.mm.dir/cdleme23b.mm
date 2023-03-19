include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "col.mm"
include "simp11l.mm"
include "hlol.mm"
include "syl.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "clat.mm"
include "hllat.mm"
include "simp2l.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcl.mm"
include "latmassOLD.mm"
include "syl13anc.mm"
include "latlej1.mm"
include "wb.mm"
include "latleeqm1.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "atbase.mm"
include "latjjdir.mm"
include "simp32.mm"
include "simp33.mm"
include "oveq12d.mm"
include "latjidm.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "simp12r.mm"
include "simp31.mm"
include "lhpat.mm"
include "syl222anc.mm"
include "eqeltrrd.mm"
include "syl5eqel.mm"

theorem cdleme23b
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( X e. B /\ -. X .<_ W ) /\ ( S =/= T /\ ( S .\/ ( X ./\ W ) ) = X /\ ( T .\/ ( X ./\ W ) ) = X ) ) -> V e. A )

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
    cV
    cS
    cT
    c.or
    co
    #
    @14
    c.an
    co
    #
    cA
    cdleme23.v
    @20
    @21
    cW
    c.an
    co
    #
    @22
    cA
    @20
    @21
    @21
    @14
    c.or
    co
    #
    c.an
    co
    #
    cW
    c.an
    co
    #
    @21
    @24
    cW
    c.an
    co
    #
    c.an
    co
    #
    @23
    @22
    @20
    cK
    col
    wcel
    #
    @21
    cB
    wcel
    #
    @24
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @26
    @28
    wceq
    @20
    @0
    @29
    @0
    @1
    @5
    @8
    @12
    @19
    simp11l
    #
    cK
    hlol
    syl
    @20
    @0
    @3
    @6
    @30
    @33
    @3
    @4
    @2
    @8
    @12
    @19
    simp12l
    #
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
    cK
    clat
    wcel
    #
    @30
    @14
    cB
    wcel
    #
    @31
    @20
    @0
    @37
    @33
    cK
    hllat
    syl
    #
    @36
    @20
    @37
    @10
    @32
    @38
    @39
    @9
    @10
    @11
    @19
    simp2l
    #
    @20
    @1
    @32
    @0
    @1
    @5
    @8
    @12
    @19
    simp11r
    #
    cB
    cH
    cK
    cW
    cdleme23.b
    cdleme23.h
    lhpbase
    syl
    #
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
    @21
    @14
    cdleme23.b
    cdleme23.j
    latjcl
    syl3anc
    #
    @42
    cB
    cK
    c.an
    @21
    @24
    cW
    cdleme23.b
    cdleme23.m
    latmassOLD
    syl13anc
    @20
    @25
    @21
    cW
    c.an
    @20
    @21
    @24
    c.le
    wbr
    #
    @25
    @21
    wceq
    #
    @20
    @37
    @30
    @38
    @45
    @39
    @36
    @43
    cB
    c.or
    cK
    c.le
    @21
    @14
    cdleme23.b
    cdleme23.l
    cdleme23.j
    latlej1
    syl3anc
    @20
    @37
    @30
    @31
    @45
    @46
    wb
    @39
    @36
    @44
    cB
    cK
    c.le
    c.an
    @21
    @24
    cdleme23.b
    cdleme23.l
    cdleme23.m
    latleeqm1
    syl3anc
    mpbid
    oveq1d
    @20
    @27
    @14
    @21
    c.an
    @20
    @24
    cX
    cW
    c.an
    @20
    @24
    @15
    @17
    c.or
    co
    #
    cX
    cX
    c.or
    co
    #
    cX
    @20
    @37
    cS
    cB
    wcel
    #
    cT
    cB
    wcel
    #
    @38
    @24
    @47
    wceq
    @39
    @20
    @3
    @49
    @34
    cA
    cB
    cS
    cK
    cdleme23.b
    cdleme23.a
    atbase
    syl
    @20
    @6
    @50
    @35
    cA
    cB
    cT
    cK
    cdleme23.b
    cdleme23.a
    atbase
    syl
    @43
    cB
    c.or
    cK
    cS
    cT
    @14
    cdleme23.b
    cdleme23.j
    latjjdir
    syl13anc
    @20
    @15
    cX
    @17
    cX
    c.or
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
    oveq12d
    @20
    @37
    @10
    @48
    cX
    wceq
    @39
    @40
    cB
    c.or
    cK
    cX
    cdleme23.b
    cdleme23.j
    latjidm
    syl2anc
    3eqtrd
    oveq1d
    oveq2d
    3eqtr3d
    @20
    @0
    @1
    @3
    @4
    @6
    @13
    @23
    cA
    wcel
    @33
    @41
    @34
    @3
    @4
    @2
    @8
    @12
    @19
    simp12r
    @35
    @9
    @12
    @13
    @16
    @18
    simp31
    cA
    cS
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme23.l
    cdleme23.j
    cdleme23.m
    cdleme23.a
    cdleme23.h
    lhpat
    syl222anc
    eqeltrrd
    syl5eqel
end
