include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "col.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11l.mm"
include "hlol.mm"
include "syl.mm"
include "simp12l.mm"
include "simp2l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "simp3l.mm"
include "atbase.mm"
include "latmassOLD.mm"
include "syl13anc.mm"
include "lhpmat.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "oveq1d.mm"
include "simp2r.mm"
include "atmod4i2.mm"
include "syl131anc.mm"
include "olj02.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"
include "simp3r.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "latleeqm2.mm"
include "mpbid.mm"
include "oveq2d.mm"
include "simp13.mm"
include "cal.mm"
include "hlatl.mm"
include "atnem0.mm"

theorem lhp2at0
  let cA: class A
  let cP: class P
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume lhp2at0.l: |- .<_ = ( le ` K )
  assume lhp2at0.j: |- .\/ = ( join ` K )
  assume lhp2at0.m: |- ./\ = ( meet ` K )
  assume lhp2at0.z: |- .0. = ( 0. ` K )
  assume lhp2at0.a: |- A = ( Atoms ` K )
  assume lhp2at0.h: |- H = ( LHyp ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ U =/= V ) /\ ( U e. A /\ U .<_ W ) /\ ( V e. A /\ V .<_ W ) ) -> ( ( P .\/ U ) ./\ V ) = .0. )

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
    cU
    cV
    wne
    #
    w3a
    #
    cU
    cA
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    wa
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cP
    cU
    c.or
    co
    #
    cW
    cV
    c.an
    co
    #
    c.an
    co
    #
    cU
    cV
    c.an
    co
    #
    @15
    cV
    c.an
    co
    c.0
    @14
    @15
    cW
    c.an
    co
    #
    cV
    c.an
    co
    #
    @17
    @18
    @14
    cK
    col
    wcel
    #
    @15
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @22
    wcel
    #
    cV
    @22
    wcel
    #
    @20
    @17
    wceq
    @14
    @0
    @21
    @0
    @1
    @5
    @6
    @10
    @13
    simp11l
    #
    cK
    hlol
    syl
    #
    @14
    @0
    @3
    @8
    @23
    @26
    @3
    @4
    @2
    @6
    @10
    @13
    simp12l
    #
    @7
    @8
    @9
    @13
    simp2l
    #
    cA
    @22
    c.or
    cK
    cP
    cU
    @22
    eqid
    #
    lhp2at0.j
    lhp2at0.a
    hlatjcl
    syl3anc
    @14
    @1
    @24
    @0
    @1
    @5
    @6
    @10
    @13
    simp11r
    @22
    cH
    cK
    cW
    @30
    lhp2at0.h
    lhpbase
    syl
    #
    @14
    @11
    @25
    @7
    @10
    @11
    @12
    simp3l
    #
    cA
    @22
    cV
    cK
    @30
    lhp2at0.a
    atbase
    syl
    #
    @22
    cK
    c.an
    @15
    cW
    cV
    @30
    lhp2at0.m
    latmassOLD
    syl13anc
    @14
    @19
    cU
    cV
    c.an
    @14
    cP
    cW
    c.an
    co
    #
    cU
    c.or
    co
    #
    c.0
    cU
    c.or
    co
    #
    @19
    cU
    @14
    @34
    c.0
    cU
    c.or
    @7
    @10
    @34
    c.0
    wceq
    #
    @13
    @2
    @5
    @37
    @6
    cA
    cP
    cH
    cK
    c.le
    c.an
    cW
    c.0
    lhp2at0.l
    lhp2at0.m
    lhp2at0.z
    lhp2at0.a
    lhp2at0.h
    lhpmat
    3adant3
    3ad2ant1
    oveq1d
    @14
    @0
    @3
    cU
    @22
    wcel
    #
    @24
    @9
    @35
    @19
    wceq
    @26
    @28
    @14
    @8
    @38
    @29
    cA
    @22
    cU
    cK
    @30
    lhp2at0.a
    atbase
    syl
    #
    @31
    @7
    @8
    @9
    @13
    simp2r
    cA
    @22
    cP
    c.or
    cK
    c.le
    c.an
    cU
    cW
    @30
    lhp2at0.l
    lhp2at0.j
    lhp2at0.m
    lhp2at0.a
    atmod4i2
    syl131anc
    @14
    @21
    @38
    @36
    cU
    wceq
    @27
    @39
    @22
    c.or
    cK
    cU
    c.0
    @30
    lhp2at0.j
    lhp2at0.z
    olj02
    syl2anc
    3eqtr3d
    oveq1d
    eqtr3d
    @14
    @16
    cV
    @15
    c.an
    @14
    @12
    @16
    cV
    wceq
    #
    @7
    @10
    @11
    @12
    simp3r
    @14
    cK
    clat
    wcel
    #
    @25
    @24
    @12
    @40
    wb
    @14
    @0
    @41
    @26
    cK
    hllat
    syl
    @33
    @31
    @22
    cK
    c.le
    c.an
    cV
    cW
    @30
    lhp2at0.l
    lhp2at0.m
    latleeqm2
    syl3anc
    mpbid
    oveq2d
    @14
    @6
    @18
    c.0
    wceq
    #
    @2
    @5
    @6
    @10
    @13
    simp13
    @14
    cK
    cal
    wcel
    #
    @8
    @11
    @6
    @42
    wb
    @14
    @0
    @43
    @26
    cK
    hlatl
    syl
    @29
    @32
    cA
    cU
    cV
    cK
    c.an
    c.0
    lhp2at0.m
    lhp2at0.z
    lhp2at0.a
    atnem0
    syl3anc
    mpbid
    3eqtr3d
end
