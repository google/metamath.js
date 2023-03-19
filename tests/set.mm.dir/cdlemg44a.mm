include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wne.mm"
include "cjn.mm"
include "co.mm"
include "cmee.mm"
include "clat.mm"
include "cbs.mm"
include "wceq.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "simp22.mm"
include "simp23l.mm"
include "eqid.mm"
include "atbase.mm"
include "ltrncl.mm"
include "syl3anc.mm"
include "simp21.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "latmcom.mm"
include "simp23.mm"
include "simp32.mm"
include "simp33.mm"
include "cdlemg43.mm"
include "syl123anc.mm"
include "simp31.mm"
include "necomd.mm"
include "3eqtr4d.mm"

theorem cdlemg44a
  let cA: class A
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cW: class W
  assume cdlemg44.h: |- H = ( LHyp ` K )
  assume cdlemg44.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg44.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg44.l: |- .<_ = ( le ` K )
  assume cdlemg44.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T /\ ( P e. A /\ -. P .<_ W ) ) /\ ( ( F ` P ) =/= P /\ ( G ` P ) =/= P /\ ( R ` F ) =/= ( R ` G ) ) ) -> ( F ` ( G ` P ) ) = ( G ` ( F ` P ) ) )

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
    cF
    cfv
    #
    cP
    wne
    #
    cP
    cG
    cfv
    #
    cP
    wne
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wne
    #
    w3a
    #
    w3a
    #
    @11
    @13
    cK
    cjn
    cfv
    #
    co
    #
    @9
    @14
    @18
    co
    #
    cK
    cmee
    cfv
    #
    co
    #
    @20
    @19
    @21
    co
    #
    @11
    cF
    cfv
    #
    @9
    cG
    cfv
    #
    @17
    cK
    clat
    wcel
    #
    @19
    cK
    cbs
    cfv
    #
    wcel
    #
    @20
    @27
    wcel
    #
    @22
    @23
    wceq
    @17
    @0
    @26
    @0
    @1
    @8
    @16
    simp1l
    cK
    hllat
    syl
    #
    @17
    @26
    @11
    @27
    wcel
    #
    @13
    @27
    wcel
    #
    @28
    @30
    @17
    @2
    @4
    cP
    @27
    wcel
    #
    @31
    @2
    @8
    @16
    simp1
    #
    @2
    @3
    @4
    @7
    @16
    simp22
    #
    @17
    @5
    @33
    @5
    @6
    @3
    @4
    @2
    @16
    simp23l
    cA
    @27
    cP
    cK
    @27
    eqid
    #
    cdlemg44.a
    atbase
    syl
    #
    @27
    cT
    cG
    cH
    cK
    chlt
    cW
    cP
    @36
    cdlemg44.h
    cdlemg44.t
    ltrncl
    syl3anc
    @17
    @2
    @3
    @32
    @34
    @2
    @3
    @4
    @7
    @16
    simp21
    #
    @27
    cR
    cT
    cF
    cH
    cK
    cW
    @36
    cdlemg44.h
    cdlemg44.t
    cdlemg44.r
    trlcl
    syl2anc
    @27
    @18
    cK
    @11
    @13
    @36
    @18
    eqid
    #
    latjcl
    syl3anc
    @17
    @26
    @9
    @27
    wcel
    #
    @14
    @27
    wcel
    #
    @29
    @30
    @17
    @2
    @3
    @33
    @40
    @34
    @38
    @37
    @27
    cT
    cF
    cH
    cK
    chlt
    cW
    cP
    @36
    cdlemg44.h
    cdlemg44.t
    ltrncl
    syl3anc
    @17
    @2
    @4
    @41
    @34
    @35
    @27
    cR
    cT
    cG
    cH
    cK
    cW
    @36
    cdlemg44.h
    cdlemg44.t
    cdlemg44.r
    trlcl
    syl2anc
    @27
    @18
    cK
    @9
    @14
    @36
    @39
    latjcl
    syl3anc
    @27
    cK
    @21
    @19
    @20
    @36
    @21
    eqid
    #
    latmcom
    syl3anc
    @17
    @2
    @3
    @4
    @7
    @12
    @15
    @24
    @22
    wceq
    @34
    @38
    @35
    @2
    @3
    @4
    @7
    @16
    simp23
    #
    @2
    @8
    @10
    @12
    @15
    simp32
    @2
    @8
    @10
    @12
    @15
    simp33
    #
    cA
    cP
    cR
    cT
    cF
    cG
    cH
    @18
    cK
    c.le
    @21
    cW
    cdlemg44.l
    @39
    cdlemg44.a
    cdlemg44.h
    cdlemg44.t
    cdlemg44.r
    @42
    cdlemg43
    syl123anc
    @17
    @2
    @4
    @3
    @7
    @10
    @14
    @13
    wne
    @25
    @23
    wceq
    @34
    @35
    @38
    @43
    @2
    @8
    @10
    @12
    @15
    simp31
    @17
    @13
    @14
    @44
    necomd
    cA
    cP
    cR
    cT
    cG
    cF
    cH
    @18
    cK
    c.le
    @21
    cW
    cdlemg44.l
    @39
    cdlemg44.a
    cdlemg44.h
    cdlemg44.t
    cdlemg44.r
    @42
    cdlemg43
    syl123anc
    3eqtr4d
end
