include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp32l.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "simp31.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "simp33l.mm"
include "ltrnat.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "trlcnv.mm"
include "necomd.mm"
include "eqnetrd.mm"
include "simp32r.mm"
include "trlcone.mm"
include "syl122anc.mm"
include "ltrncom.mm"
include "fveq2d.mm"
include "3netr3d.mm"
include "simp33.mm"
include "ltrnel.mm"
include "simprd.mm"
include "trlle.mm"
include "ltrnco.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "hlatjcl.mm"
include "lattr.mm"
include "mpan2d.mm"
include "mtod.mm"
include "2llnma2.mm"
include "syl132anc.mm"

theorem cdlemk3
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( ( R ` G ) =/= ( R ` F ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( ( F ` P ) .\/ ( R ` F ) ) ./\ ( ( F ` P ) .\/ ( R ` ( G o. `' F ) ) ) ) = ( F ` P ) )

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
    cG
    cT
    wcel
    #
    wa
    #
    cG
    cR
    cfv
    #
    cF
    cR
    cfv
    #
    wne
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cG
    @9
    wne
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
    w3a
    #
    w3a
    #
    @0
    @7
    cA
    wcel
    #
    cG
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    cA
    wcel
    #
    cP
    cF
    cfv
    #
    cA
    wcel
    #
    @7
    @21
    wne
    @23
    @7
    @21
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @23
    @7
    c.or
    co
    @23
    @21
    c.or
    co
    c.an
    co
    @23
    wceq
    @0
    @1
    @5
    @16
    simp1l
    #
    @17
    @2
    @3
    @10
    @18
    @2
    @5
    @16
    simp1
    #
    @2
    @3
    @4
    @16
    simp2l
    #
    @10
    @11
    @8
    @15
    @2
    @5
    simp32l
    cA
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemk.b
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlnidat
    syl3anc
    #
    @17
    @2
    @4
    @3
    @8
    @22
    @28
    @2
    @3
    @4
    @16
    simp2r
    #
    @29
    @2
    @5
    @8
    @12
    @15
    simp31
    #
    cA
    cR
    cT
    cG
    cF
    cH
    cK
    cW
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcocnvat
    syl121anc
    #
    @17
    @2
    @3
    @13
    @24
    @28
    @29
    @13
    @14
    @8
    @12
    @2
    @5
    simp33l
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnat
    syl3anc
    #
    @17
    @19
    cR
    cfv
    #
    @19
    cG
    ccom
    #
    cR
    cfv
    #
    @7
    @21
    @17
    @2
    @19
    cT
    wcel
    #
    @4
    @35
    @6
    wne
    @11
    @35
    @37
    wne
    @28
    @17
    @2
    @3
    @38
    @28
    @29
    cT
    cF
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncnv
    syl2anc
    #
    @31
    @17
    @35
    @7
    @6
    @17
    @2
    @3
    @35
    @7
    wceq
    @28
    @29
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcnv
    syl2anc
    #
    @17
    @6
    @7
    @32
    necomd
    eqnetrd
    @10
    @11
    @8
    @15
    @2
    @5
    simp32r
    cB
    cR
    cT
    @19
    cG
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcone
    syl122anc
    @40
    @17
    @36
    @20
    cR
    @17
    @2
    @38
    @4
    @36
    @20
    wceq
    @28
    @39
    @31
    cT
    @19
    cG
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncom
    syl3anc
    fveq2d
    3netr3d
    @17
    @26
    @23
    cW
    c.le
    wbr
    #
    @17
    @2
    @3
    @15
    @41
    wn
    #
    @28
    @29
    @2
    @5
    @8
    @12
    @15
    simp33
    @2
    @3
    @15
    w3a
    @24
    @42
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.a
    cdlemk.h
    cdlemk.t
    ltrnel
    simprd
    syl3anc
    @17
    @26
    @25
    cW
    c.le
    wbr
    #
    @41
    @17
    @7
    cW
    c.le
    wbr
    #
    @21
    cW
    c.le
    wbr
    #
    @43
    @17
    @2
    @3
    @44
    @28
    @29
    cR
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlle
    syl2anc
    @17
    @2
    @20
    cT
    wcel
    #
    @45
    @28
    @17
    @2
    @4
    @38
    @46
    @28
    @31
    @39
    cT
    cG
    @19
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    cR
    cT
    @20
    cH
    cK
    c.le
    cW
    cdlemk.l
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlle
    syl2anc
    @17
    cK
    clat
    wcel
    #
    @7
    cB
    wcel
    #
    @21
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @44
    @45
    wa
    @43
    wb
    @17
    @0
    @47
    @27
    cK
    hllat
    syl
    #
    @17
    @18
    @48
    @30
    cA
    cB
    @7
    cK
    cdlemk.b
    cdlemk.a
    atbase
    syl
    @17
    @22
    @49
    @33
    cA
    cB
    @21
    cK
    cdlemk.b
    cdlemk.a
    atbase
    syl
    @17
    @1
    @50
    @0
    @1
    @5
    @16
    simp1r
    cB
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    lhpbase
    syl
    #
    cB
    c.or
    cK
    c.le
    @7
    @21
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    latjle12
    syl13anc
    mpbi2and
    @17
    @47
    @23
    cB
    wcel
    #
    @25
    cB
    wcel
    #
    @50
    @26
    @43
    wa
    @41
    wi
    @51
    @17
    @24
    @53
    @34
    cA
    cB
    @23
    cK
    cdlemk.b
    cdlemk.a
    atbase
    syl
    @17
    @0
    @18
    @22
    @54
    @27
    @30
    @33
    cA
    cB
    c.or
    cK
    @7
    @21
    cdlemk.b
    cdlemk.j
    cdlemk.a
    hlatjcl
    syl3anc
    @52
    cB
    cK
    c.le
    @23
    @25
    cW
    cdlemk.b
    cdlemk.l
    lattr
    syl13anc
    mpan2d
    mtod
    cA
    @7
    @21
    @23
    c.or
    cK
    c.le
    c.an
    cdlemk.l
    cdlemk.j
    cdlemk.m
    cdlemk.a
    2llnma2
    syl132anc
end
