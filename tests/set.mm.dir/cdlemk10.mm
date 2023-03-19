include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp1.mm"
include "simp22.mm"
include "simp21.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "trlle.mm"
include "simp23.mm"
include "clat.mm"
include "wb.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "trlcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "latjcl.mm"
include "simp3l.mm"
include "ltrnat.mm"
include "hlatjcl.mm"
include "latmlem2.mm"
include "mpd.mm"
include "wceq.mm"
include "simp3.mm"
include "cdlemk9.mm"
include "syl221anc.mm"
include "breqtrd.mm"
include "syl5eqbr.mm"

theorem cdlemk10
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
  let cV: class V
  let cW: class W
  let cX: class X
  assume cdlemk.b: |- B = ( Base ` K )
  assume cdlemk.l: |- .<_ = ( le ` K )
  assume cdlemk.j: |- .\/ = ( join ` K )
  assume cdlemk.a: |- A = ( Atoms ` K )
  assume cdlemk.h: |- H = ( LHyp ` K )
  assume cdlemk.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk.m: |- ./\ = ( meet ` K )
  assume cdlemk.v1: |- V = ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' F ) ) .\/ ( R ` ( X o. `' F ) ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> V .<_ ( R ` ( X o. `' G ) ) )

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
    cX
    cT
    wcel
    #
    w3a
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
    cV
    cP
    cG
    cfv
    #
    cP
    cX
    cfv
    #
    c.or
    co
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
    cX
    @14
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    cX
    cG
    ccnv
    ccom
    cR
    cfv
    #
    c.le
    cdlemk.v1
    @10
    @20
    @13
    cW
    c.an
    co
    #
    @21
    c.le
    @10
    @19
    cW
    c.le
    wbr
    #
    @20
    @22
    c.le
    wbr
    #
    @10
    @16
    cW
    c.le
    wbr
    #
    @18
    cW
    c.le
    wbr
    #
    @23
    @10
    @2
    @15
    cT
    wcel
    #
    @25
    @2
    @6
    @9
    simp1
    #
    @10
    @2
    @4
    @14
    cT
    wcel
    #
    @27
    @28
    @2
    @3
    @4
    @5
    @9
    simp22
    #
    @10
    @2
    @3
    @29
    @28
    @2
    @3
    @4
    @5
    @9
    simp21
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
    cT
    cG
    @14
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    #
    cR
    cT
    @15
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
    @10
    @2
    @17
    cT
    wcel
    #
    @26
    @28
    @10
    @2
    @5
    @29
    @33
    @28
    @2
    @3
    @4
    @5
    @9
    simp23
    #
    @31
    cT
    cX
    @14
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    #
    cR
    cT
    @17
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
    @10
    cK
    clat
    wcel
    #
    @16
    cB
    wcel
    #
    @18
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @25
    @26
    wa
    @23
    wb
    @10
    @0
    @36
    @0
    @1
    @6
    @9
    simp1l
    #
    cK
    hllat
    syl
    #
    @10
    @2
    @27
    @37
    @28
    @32
    cB
    cR
    cT
    @15
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcl
    syl2anc
    #
    @10
    @2
    @33
    @38
    @28
    @35
    cB
    cR
    cT
    @17
    cH
    cK
    cW
    cdlemk.b
    cdlemk.h
    cdlemk.t
    cdlemk.r
    trlcl
    syl2anc
    #
    @10
    @1
    @39
    @0
    @1
    @6
    @9
    simp1r
    #
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
    @16
    @18
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    latjle12
    syl13anc
    mpbi2and
    @10
    @36
    @19
    cB
    wcel
    #
    @39
    @13
    cB
    wcel
    #
    @23
    @24
    wi
    @41
    @10
    @36
    @37
    @38
    @46
    @41
    @42
    @43
    cB
    c.or
    cK
    @16
    @18
    cdlemk.b
    cdlemk.j
    latjcl
    syl3anc
    @45
    @10
    @0
    @11
    cA
    wcel
    #
    @12
    cA
    wcel
    #
    @47
    @40
    @10
    @2
    @4
    @7
    @48
    @28
    @30
    @2
    @6
    @7
    @8
    simp3l
    #
    cA
    cP
    cT
    cG
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
    @10
    @2
    @5
    @7
    @49
    @28
    @34
    @50
    cA
    cP
    cT
    cX
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
    cA
    cB
    c.or
    cK
    @11
    @12
    cdlemk.b
    cdlemk.j
    cdlemk.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @19
    cW
    @13
    cdlemk.b
    cdlemk.l
    cdlemk.m
    latmlem2
    syl13anc
    mpd
    @10
    @0
    @1
    @4
    @5
    @9
    @22
    @21
    wceq
    @40
    @44
    @30
    @34
    @2
    @6
    @9
    simp3
    cA
    cB
    cP
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk9
    syl221anc
    breqtrd
    syl5eqbr
end
