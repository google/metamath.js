include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cmee.mm"
include "cp1.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "ltrnat.mm"
include "3adant3r.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp3l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp1.mm"
include "simp2.mm"
include "ltrncl.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latlej2.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "ltrnel.mm"
include "lhpjat1.mm"
include "syl21anc.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtrrd.mm"
include "trlval2.mm"
include "oveq1d.mm"
include "trlcl.mm"
include "latjcom.mm"
include "3eqtr2rd.mm"

theorem trljat2
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume trljat.l: |- .<_ = ( le ` K )
  assume trljat.j: |- .\/ = ( join ` K )
  assume trljat.a: |- A = ( Atoms ` K )
  assume trljat.h: |- H = ( LHyp ` K )
  assume trljat.t: |- T = ( ( LTrn ` K ) ` W )
  assume trljat.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( F ` P ) .\/ ( R ` F ) ) = ( P .\/ ( F ` P ) ) )

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
    cF
    cT
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
    cF
    cfv
    #
    c.or
    co
    #
    @9
    cW
    cK
    cmee
    cfv
    #
    co
    #
    @8
    c.or
    co
    #
    cF
    cR
    cfv
    #
    @8
    c.or
    co
    #
    @8
    @13
    c.or
    co
    #
    @7
    @12
    @9
    cW
    @8
    c.or
    co
    #
    @10
    co
    #
    @9
    cK
    cp1
    cfv
    #
    @10
    co
    #
    @9
    @7
    @0
    @8
    cA
    wcel
    #
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @21
    wcel
    #
    @8
    @9
    c.le
    wbr
    #
    @12
    @17
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
    @20
    @5
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    trljat.l
    trljat.a
    trljat.h
    trljat.t
    ltrnat
    3adant3r
    @7
    cK
    clat
    wcel
    #
    cP
    @21
    wcel
    #
    @8
    @21
    wcel
    #
    @22
    @7
    @0
    @26
    @25
    cK
    hllat
    syl
    #
    @7
    @4
    @27
    @2
    @3
    @4
    @5
    simp3l
    cA
    @21
    cP
    cK
    @21
    eqid
    #
    trljat.a
    atbase
    syl
    #
    @7
    @2
    @3
    @27
    @28
    @2
    @3
    @6
    simp1
    #
    @2
    @3
    @6
    simp2
    #
    @31
    @21
    cT
    cF
    cH
    cK
    chlt
    cW
    cP
    @30
    trljat.h
    trljat.t
    ltrncl
    syl3anc
    #
    @21
    c.or
    cK
    cP
    @8
    @30
    trljat.j
    latjcl
    syl3anc
    #
    @7
    @1
    @23
    @0
    @1
    @3
    @6
    simp1r
    #
    @21
    cH
    cK
    cW
    @30
    trljat.h
    lhpbase
    syl
    @7
    @26
    @27
    @28
    @24
    @29
    @31
    @34
    @21
    c.or
    cK
    c.le
    cP
    @8
    @30
    trljat.l
    trljat.j
    latlej2
    syl3anc
    cA
    @21
    @8
    c.or
    cK
    c.le
    @10
    @9
    cW
    @30
    trljat.l
    trljat.j
    @10
    eqid
    #
    trljat.a
    atmod2i1
    syl131anc
    @7
    @16
    @18
    @9
    @10
    @7
    @0
    @1
    @20
    @8
    cW
    c.le
    wbr
    wn
    wa
    @16
    @18
    wceq
    @25
    @36
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    trljat.l
    trljat.a
    trljat.h
    trljat.t
    ltrnel
    cA
    @8
    @18
    cH
    c.or
    cK
    c.le
    cW
    trljat.l
    trljat.j
    @18
    eqid
    #
    trljat.a
    trljat.h
    lhpjat1
    syl21anc
    oveq2d
    @7
    cK
    col
    wcel
    #
    @22
    @19
    @9
    wceq
    @7
    @0
    @39
    @25
    cK
    hlol
    syl
    @35
    @21
    @18
    cK
    @10
    @9
    @30
    @37
    @38
    olm11
    syl2anc
    3eqtrrd
    @7
    @13
    @11
    @8
    c.or
    cA
    cP
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    @10
    cW
    trljat.l
    trljat.j
    @37
    trljat.a
    trljat.h
    trljat.t
    trljat.r
    trlval2
    oveq1d
    @7
    @26
    @13
    @21
    wcel
    #
    @28
    @14
    @15
    wceq
    @29
    @7
    @2
    @3
    @40
    @32
    @33
    @21
    cR
    cT
    cF
    cH
    cK
    cW
    @30
    trljat.h
    trljat.t
    trljat.r
    trlcl
    syl2anc
    @34
    @21
    c.or
    cK
    @13
    @8
    @30
    trljat.j
    latjcom
    syl3anc
    3eqtr2rd
end
