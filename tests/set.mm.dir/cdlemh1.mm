include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "wne.mm"
include "ccnv.mm"
include "ccom.mm"
include "oveq1i.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp11.mm"
include "simp13.mm"
include "simp12.mm"
include "simp3r.mm"
include "necomd.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp2l.mm"
include "atbase.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp2r.mm"
include "hlatjcl.mm"
include "hlatlej2.mm"
include "atmod4i1.mm"
include "syl131anc.mm"
include "ltrncnv.mm"
include "trljco2.mm"
include "trlcnv.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ltrnco.mm"
include "latjass.mm"
include "syl13anc.mm"
include "3eqtr4d.mm"
include "simp3l.mm"
include "wi.mm"
include "latjlej1.mm"
include "mpd.mm"
include "wb.mm"
include "latleeqm2.mm"
include "mpbid.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem cdlemh1
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemh.b: |- B = ( Base ` K )
  assume cdlemh.l: |- .<_ = ( le ` K )
  assume cdlemh.j: |- .\/ = ( join ` K )
  assume cdlemh.m: |- ./\ = ( meet ` K )
  assume cdlemh.a: |- A = ( Atoms ` K )
  assume cdlemh.h: |- H = ( LHyp ` K )
  assume cdlemh.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemh.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemh.s: |- S = ( ( P .\/ ( R ` G ) ) ./\ ( Q .\/ ( R ` ( G o. `' F ) ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( P e. A /\ Q e. A ) /\ ( Q .<_ ( P .\/ ( R ` F ) ) /\ ( R ` F ) =/= ( R ` G ) ) ) -> ( S .\/ ( R ` ( G o. `' F ) ) ) = ( Q .\/ ( R ` ( G o. `' F ) ) ) )

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
    w3a
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    wa
    #
    cQ
    cP
    cF
    cR
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    @9
    cG
    cR
    cfv
    #
    wne
    #
    wa
    #
    w3a
    #
    cS
    cG
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    cP
    @12
    c.or
    co
    #
    cQ
    @18
    c.or
    co
    #
    c.an
    co
    #
    @18
    c.or
    co
    #
    @20
    cS
    @21
    @18
    c.or
    cdlemh.s
    oveq1i
    @15
    @22
    @19
    @18
    c.or
    co
    #
    @20
    c.an
    co
    #
    @10
    @18
    c.or
    co
    #
    @20
    c.an
    co
    #
    @20
    @15
    @0
    @18
    cA
    wcel
    #
    @19
    cB
    wcel
    #
    @20
    cB
    wcel
    #
    @18
    @20
    c.le
    wbr
    #
    @22
    @24
    wceq
    @0
    @1
    @3
    @4
    @8
    @14
    simp11l
    #
    @15
    @2
    @4
    @3
    @12
    @9
    wne
    @27
    @2
    @3
    @4
    @8
    @14
    simp11
    #
    @2
    @3
    @4
    @8
    @14
    simp13
    #
    @2
    @3
    @4
    @8
    @14
    simp12
    #
    @15
    @9
    @12
    @5
    @8
    @11
    @13
    simp3r
    necomd
    cA
    cR
    cT
    cG
    cF
    cH
    cK
    cW
    cdlemh.a
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcocnvat
    syl121anc
    #
    @15
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @28
    @15
    @0
    @36
    @31
    cK
    hllat
    syl
    #
    @15
    @6
    @37
    @5
    @6
    @7
    @14
    simp2l
    cA
    cB
    cP
    cK
    cdlemh.b
    cdlemh.a
    atbase
    syl
    #
    @15
    @2
    @4
    @38
    @32
    @33
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcl
    syl2anc
    #
    cB
    c.or
    cK
    cP
    @12
    cdlemh.b
    cdlemh.j
    latjcl
    syl3anc
    @15
    @0
    @7
    @27
    @29
    @31
    @5
    @6
    @7
    @14
    simp2r
    #
    @35
    cA
    cB
    c.or
    cK
    cQ
    @18
    cdlemh.b
    cdlemh.j
    cdlemh.a
    hlatjcl
    syl3anc
    #
    @15
    @0
    @7
    @27
    @30
    @31
    @42
    @35
    cA
    cQ
    @18
    c.or
    cK
    c.le
    cdlemh.l
    cdlemh.j
    cdlemh.a
    hlatlej2
    syl3anc
    cA
    cB
    @18
    c.or
    cK
    c.le
    c.an
    @19
    @20
    cdlemh.b
    cdlemh.l
    cdlemh.j
    cdlemh.m
    cdlemh.a
    atmod4i1
    syl131anc
    @15
    @23
    @25
    @20
    c.an
    @15
    cP
    @12
    @18
    c.or
    co
    #
    c.or
    co
    #
    cP
    @9
    @18
    c.or
    co
    #
    c.or
    co
    #
    @23
    @25
    @15
    @44
    @46
    cP
    c.or
    @15
    @44
    @16
    cR
    cfv
    #
    @18
    c.or
    co
    #
    @46
    @15
    @2
    @4
    @16
    cT
    wcel
    #
    @44
    @49
    wceq
    @32
    @33
    @15
    @2
    @3
    @50
    @32
    @34
    cT
    cF
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    ltrncnv
    syl2anc
    #
    cR
    cT
    cG
    @16
    cH
    c.or
    cK
    cW
    cdlemh.j
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trljco2
    syl3anc
    @15
    @48
    @9
    @18
    c.or
    @15
    @2
    @3
    @48
    @9
    wceq
    @32
    @34
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcnv
    syl2anc
    oveq1d
    eqtrd
    oveq2d
    @15
    @36
    @37
    @38
    @18
    cB
    wcel
    #
    @23
    @45
    wceq
    @39
    @40
    @41
    @15
    @2
    @17
    cT
    wcel
    #
    @52
    @32
    @15
    @2
    @4
    @50
    @53
    @32
    @33
    @51
    cT
    cG
    @16
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @17
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcl
    syl2anc
    #
    cB
    c.or
    cK
    cP
    @12
    @18
    cdlemh.b
    cdlemh.j
    latjass
    syl13anc
    @15
    @36
    @37
    @9
    cB
    wcel
    #
    @52
    @25
    @47
    wceq
    @39
    @40
    @15
    @2
    @3
    @55
    @32
    @34
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcl
    syl2anc
    #
    @54
    cB
    c.or
    cK
    cP
    @9
    @18
    cdlemh.b
    cdlemh.j
    latjass
    syl13anc
    3eqtr4d
    oveq1d
    @15
    @20
    @25
    c.le
    wbr
    #
    @26
    @20
    wceq
    #
    @15
    @11
    @57
    @5
    @8
    @11
    @13
    simp3l
    @15
    @36
    cQ
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @52
    @11
    @57
    wi
    @39
    @15
    @7
    @59
    @42
    cA
    cB
    cQ
    cK
    cdlemh.b
    cdlemh.a
    atbase
    syl
    @15
    @36
    @37
    @55
    @60
    @39
    @40
    @56
    cB
    c.or
    cK
    cP
    @9
    cdlemh.b
    cdlemh.j
    latjcl
    syl3anc
    #
    @54
    cB
    c.or
    cK
    c.le
    cQ
    @10
    @18
    cdlemh.b
    cdlemh.l
    cdlemh.j
    latjlej1
    syl13anc
    mpd
    @15
    @36
    @29
    @25
    cB
    wcel
    #
    @57
    @58
    wb
    @39
    @43
    @15
    @36
    @60
    @52
    @62
    @39
    @61
    @54
    cB
    c.or
    cK
    @10
    @18
    cdlemh.b
    cdlemh.j
    latjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @20
    @25
    cdlemh.b
    cdlemh.l
    cdlemh.m
    latleeqm2
    syl3anc
    mpbid
    3eqtrd
    syl5eq
end
