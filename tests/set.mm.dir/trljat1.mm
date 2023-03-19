include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cmee.mm"
include "eqid.mm"
include "trlval2.mm"
include "oveq1d.mm"
include "clat.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp3l.mm"
include "atbase.mm"
include "trlcl.mm"
include "3adant3.mm"
include "latjcom.mm"
include "syl3anc.mm"
include "cp1.mm"
include "ltrncl.mm"
include "syld3an3.mm"
include "latjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latlej1.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "lhpjat1.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtrrd.mm"
include "3eqtr4d.mm"

theorem trljat1
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ ( P e. A /\ -. P .<_ W ) ) -> ( P .\/ ( R ` F ) ) = ( P .\/ ( F ` P ) ) )

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
    cF
    cR
    cfv
    #
    cP
    c.or
    co
    #
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    #
    cW
    cK
    cmee
    cfv
    #
    co
    #
    cP
    c.or
    co
    #
    cP
    @8
    c.or
    co
    #
    @11
    @7
    @8
    @13
    cP
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
    @12
    cW
    trljat.l
    trljat.j
    @12
    eqid
    #
    trljat.a
    trljat.h
    trljat.t
    trljat.r
    trlval2
    oveq1d
    @7
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @8
    @18
    wcel
    #
    @15
    @9
    wceq
    @7
    @0
    @17
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
    @19
    @2
    @3
    @4
    @5
    simp3l
    #
    cA
    @18
    cP
    cK
    @18
    eqid
    #
    trljat.a
    atbase
    syl
    #
    @2
    @3
    @20
    @6
    @18
    cR
    cT
    cF
    cH
    cK
    cW
    @24
    trljat.h
    trljat.t
    trljat.r
    trlcl
    3adant3
    @18
    c.or
    cK
    cP
    @8
    @24
    trljat.j
    latjcom
    syl3anc
    @7
    @14
    @11
    cW
    cP
    c.or
    co
    #
    @12
    co
    #
    @11
    cK
    cp1
    cfv
    #
    @12
    co
    #
    @11
    @7
    @0
    @4
    @11
    @18
    wcel
    #
    cW
    @18
    wcel
    #
    cP
    @11
    c.le
    wbr
    #
    @14
    @27
    wceq
    @21
    @23
    @7
    @17
    @19
    @10
    @18
    wcel
    #
    @30
    @22
    @25
    @2
    @3
    @6
    @19
    @33
    @25
    @18
    cT
    cF
    cH
    cK
    chlt
    cW
    cP
    @24
    trljat.h
    trljat.t
    ltrncl
    syld3an3
    #
    @18
    c.or
    cK
    cP
    @10
    @24
    trljat.j
    latjcl
    syl3anc
    #
    @7
    @1
    @31
    @0
    @1
    @3
    @6
    simp1r
    @18
    cH
    cK
    cW
    @24
    trljat.h
    lhpbase
    syl
    @7
    @17
    @19
    @33
    @32
    @22
    @25
    @34
    @18
    c.or
    cK
    c.le
    cP
    @10
    @24
    trljat.l
    trljat.j
    latlej1
    syl3anc
    cA
    @18
    cP
    c.or
    cK
    c.le
    @12
    @11
    cW
    @24
    trljat.l
    trljat.j
    @16
    trljat.a
    atmod2i1
    syl131anc
    @7
    @26
    @28
    @11
    @12
    @2
    @6
    @26
    @28
    wceq
    @3
    cA
    cP
    @28
    cH
    c.or
    cK
    c.le
    cW
    trljat.l
    trljat.j
    @28
    eqid
    #
    trljat.a
    trljat.h
    lhpjat1
    3adant2
    oveq2d
    @7
    cK
    col
    wcel
    #
    @30
    @29
    @11
    wceq
    @7
    @0
    @37
    @21
    cK
    hlol
    syl
    @35
    @18
    @28
    cK
    @12
    @11
    @24
    @16
    @36
    olm11
    syl2anc
    3eqtrrd
    3eqtr4d
end
