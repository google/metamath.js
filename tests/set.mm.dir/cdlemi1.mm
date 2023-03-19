include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "tendocl.mm"
include "syl3anc.mm"
include "simp3l.mm"
include "atbase.mm"
include "ltrncl.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "latlej2.mm"
include "wceq.mm"
include "trlval2.mm"
include "syld3an2.mm"
include "oveq2d.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latlej1.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "cp1.mm"
include "eqid.mm"
include "lhpjat2.mm"
include "3adant2.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "breqtrrd.mm"
include "tendotp.mm"
include "wi.mm"
include "latjlej2.mm"
include "syl13anc.mm"
include "mpd.mm"
include "lattrd.mm"

theorem cdlemi1
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemi.b: |- B = ( Base ` K )
  assume cdlemi.l: |- .<_ = ( le ` K )
  assume cdlemi.j: |- .\/ = ( join ` K )
  assume cdlemi.m: |- ./\ = ( meet ` K )
  assume cdlemi.a: |- A = ( Atoms ` K )
  assume cdlemi.h: |- H = ( LHyp ` K )
  assume cdlemi.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemi.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemi.e: |- E = ( ( TEndo ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( U e. E /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( U ` G ) ` P ) .<_ ( P .\/ ( R ` G ) ) )

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
    cU
    cE
    wcel
    #
    cG
    cT
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
    w3a
    #
    cB
    cK
    c.le
    cP
    cG
    cU
    cfv
    #
    cfv
    #
    cP
    @10
    cR
    cfv
    #
    c.or
    co
    #
    cP
    cG
    cR
    cfv
    #
    c.or
    co
    #
    cdlemi.b
    cdlemi.l
    @9
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @8
    simp1l
    #
    cK
    hllat
    syl
    #
    @9
    @2
    @10
    cT
    wcel
    #
    cP
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @2
    @5
    @8
    simp1
    #
    @9
    @2
    @3
    @4
    @19
    @22
    @2
    @3
    @4
    @8
    simp2l
    #
    @2
    @3
    @4
    @8
    simp2r
    #
    cU
    cT
    cE
    cG
    cH
    cK
    chlt
    cW
    cdlemi.h
    cdlemi.t
    cdlemi.e
    tendocl
    syl3anc
    #
    @9
    @6
    @20
    @2
    @5
    @6
    @7
    simp3l
    #
    cA
    cB
    cP
    cK
    cdlemi.b
    cdlemi.a
    atbase
    syl
    #
    cB
    cT
    @10
    cH
    cK
    chlt
    cW
    cP
    cdlemi.b
    cdlemi.h
    cdlemi.t
    ltrncl
    syl3anc
    #
    @9
    @16
    @20
    @12
    cB
    wcel
    #
    @13
    cB
    wcel
    @18
    @27
    @9
    @2
    @19
    @29
    @22
    @25
    cB
    cR
    cT
    @10
    cH
    cK
    cW
    cdlemi.b
    cdlemi.h
    cdlemi.t
    cdlemi.r
    trlcl
    syl2anc
    #
    cB
    c.or
    cK
    cP
    @12
    cdlemi.b
    cdlemi.j
    latjcl
    syl3anc
    @9
    @16
    @20
    @14
    cB
    wcel
    #
    @15
    cB
    wcel
    @18
    @27
    @9
    @2
    @4
    @31
    @22
    @24
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemi.b
    cdlemi.h
    cdlemi.t
    cdlemi.r
    trlcl
    syl2anc
    #
    cB
    c.or
    cK
    cP
    @14
    cdlemi.b
    cdlemi.j
    latjcl
    syl3anc
    @9
    @11
    cP
    @11
    c.or
    co
    #
    @13
    c.le
    @9
    @16
    @20
    @21
    @11
    @33
    c.le
    wbr
    @18
    @27
    @28
    cB
    c.or
    cK
    c.le
    cP
    @11
    cdlemi.b
    cdlemi.l
    cdlemi.j
    latlej2
    syl3anc
    @9
    @13
    cP
    @33
    cW
    c.an
    co
    #
    c.or
    co
    #
    @33
    cP
    cW
    c.or
    co
    #
    c.an
    co
    #
    @33
    @9
    @12
    @34
    cP
    c.or
    @2
    @19
    @5
    @8
    @12
    @34
    wceq
    @25
    cA
    cP
    cR
    cT
    @10
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemi.l
    cdlemi.j
    cdlemi.m
    cdlemi.a
    cdlemi.h
    cdlemi.t
    cdlemi.r
    trlval2
    syld3an2
    oveq2d
    @9
    @0
    @6
    @33
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    cP
    @33
    c.le
    wbr
    #
    @35
    @37
    wceq
    @17
    @26
    @9
    @16
    @20
    @21
    @38
    @18
    @27
    @28
    cB
    c.or
    cK
    cP
    @11
    cdlemi.b
    cdlemi.j
    latjcl
    syl3anc
    #
    @9
    @1
    @39
    @0
    @1
    @5
    @8
    simp1r
    cB
    cH
    cK
    cW
    cdlemi.b
    cdlemi.h
    lhpbase
    syl
    @9
    @16
    @20
    @21
    @40
    @18
    @27
    @28
    cB
    c.or
    cK
    c.le
    cP
    @11
    cdlemi.b
    cdlemi.l
    cdlemi.j
    latlej1
    syl3anc
    cA
    cB
    cP
    c.or
    cK
    c.le
    c.an
    @33
    cW
    cdlemi.b
    cdlemi.l
    cdlemi.j
    cdlemi.m
    cdlemi.a
    atmod3i1
    syl131anc
    @9
    @37
    @33
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @33
    @9
    @36
    @42
    @33
    c.an
    @2
    @8
    @36
    @42
    wceq
    @5
    cA
    cP
    @42
    cH
    c.or
    cK
    c.le
    cW
    cdlemi.l
    cdlemi.j
    @42
    eqid
    #
    cdlemi.a
    cdlemi.h
    lhpjat2
    3adant2
    oveq2d
    @9
    cK
    col
    wcel
    #
    @38
    @43
    @33
    wceq
    @9
    @0
    @45
    @17
    cK
    hlol
    syl
    @41
    cB
    @42
    cK
    c.an
    @33
    cdlemi.b
    cdlemi.m
    @44
    olm11
    syl2anc
    eqtrd
    3eqtrd
    breqtrrd
    @9
    @12
    @14
    c.le
    wbr
    #
    @13
    @15
    c.le
    wbr
    #
    @9
    @2
    @3
    @4
    @46
    @22
    @23
    @24
    cR
    cU
    cT
    cE
    cG
    cH
    cK
    c.le
    chlt
    cW
    cdlemi.l
    cdlemi.h
    cdlemi.t
    cdlemi.r
    cdlemi.e
    tendotp
    syl3anc
    @9
    @16
    @29
    @31
    @20
    @46
    @47
    wi
    @18
    @30
    @32
    @27
    cB
    c.or
    cK
    c.le
    @12
    @14
    cP
    cdlemi.b
    cdlemi.l
    cdlemi.j
    latjlej2
    syl13anc
    mpd
    lattrd
end
