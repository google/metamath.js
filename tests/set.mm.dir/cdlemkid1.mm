include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "oveq1i.mm"
include "simp1l.mm"
include "simp1.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "simp3ll.mm"
include "hlatjcl.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp22.mm"
include "atbase.mm"
include "ltrncl.mm"
include "simp21.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "trlcl.mm"
include "latjcl.mm"
include "hlatlej2.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "latj32.mm"
include "syl13anc.mm"
include "simp3l.mm"
include "trljat3.mm"
include "oveq1d.mm"
include "latjass.mm"
include "3eqtrd.mm"
include "latjcom.mm"
include "trlcnv.mm"
include "simp23.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqtr4d.mm"
include "trljco.mm"
include "3eqtr2d.mm"
include "latabs2.mm"
include "syl5eq.mm"

theorem cdlemkid1
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vb: setvar b
  assume cdlemk5.b: |- B = ( Base ` K )
  assume cdlemk5.l: |- .<_ = ( le ` K )
  assume cdlemk5.j: |- .\/ = ( join ` K )
  assume cdlemk5.m: |- ./\ = ( meet ` K )
  assume cdlemk5.a: |- A = ( Atoms ` K )
  assume cdlemk5.h: |- H = ( LHyp ` K )
  assume cdlemk5.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk5.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk5.z: |- Z = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ N e. T /\ ( R ` F ) = ( R ` N ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( b e. T /\ b =/= ( _I |` B ) ) ) ) -> ( Z .\/ ( R ` b ) ) = ( P .\/ ( R ` b ) ) )

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
    cN
    cT
    wcel
    #
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    #
    wceq
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
    vb
    cv
    #
    cT
    wcel
    #
    @12
    cid
    cB
    cres
    wne
    #
    wa
    #
    wa
    #
    w3a
    #
    cZ
    @12
    cR
    cfv
    #
    c.or
    co
    cP
    @18
    c.or
    co
    #
    cP
    cN
    cfv
    #
    @12
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
    #
    c.an
    co
    #
    @18
    c.or
    co
    #
    @19
    cZ
    @25
    @18
    c.or
    cdlemk5.z
    oveq1i
    @17
    @26
    @19
    @24
    @18
    c.or
    co
    #
    c.an
    co
    #
    @19
    @19
    @6
    c.or
    co
    #
    c.an
    co
    #
    @19
    @17
    @0
    @18
    cA
    wcel
    #
    @19
    cB
    wcel
    #
    @24
    cB
    wcel
    #
    @18
    @19
    c.le
    wbr
    #
    @26
    @28
    wceq
    @0
    @1
    @8
    @16
    simp1l
    #
    @17
    @2
    @13
    @14
    @31
    @2
    @8
    @16
    simp1
    #
    @13
    @14
    @11
    @2
    @8
    simp3rl
    #
    @13
    @14
    @11
    @2
    @8
    simp3rr
    cA
    cB
    cR
    cT
    @12
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlnidat
    syl3anc
    #
    @17
    @0
    @9
    @31
    @32
    @35
    @9
    @10
    @15
    @2
    @8
    simp3ll
    #
    @38
    cA
    cB
    c.or
    cK
    cP
    @18
    cdlemk5.b
    cdlemk5.j
    cdlemk5.a
    hlatjcl
    syl3anc
    #
    @17
    cK
    clat
    wcel
    #
    @20
    cB
    wcel
    #
    @23
    cB
    wcel
    #
    @33
    @17
    @0
    @41
    @35
    cK
    hllat
    syl
    #
    @17
    @2
    @4
    cP
    cB
    wcel
    #
    @42
    @36
    @2
    @3
    @4
    @7
    @16
    simp22
    #
    @17
    @9
    @45
    @39
    cA
    cB
    cP
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    #
    cB
    cT
    cN
    cH
    cK
    chlt
    cW
    cP
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    ltrncl
    syl3anc
    #
    @17
    @2
    @22
    cT
    wcel
    #
    @43
    @36
    @17
    @2
    @13
    @21
    cT
    wcel
    #
    @49
    @36
    @37
    @17
    @2
    @3
    @50
    @36
    @2
    @3
    @4
    @7
    @16
    simp21
    #
    cT
    cF
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrncnv
    syl2anc
    #
    cT
    @12
    @21
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @22
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcl
    syl2anc
    #
    cB
    c.or
    cK
    @20
    @23
    cdlemk5.b
    cdlemk5.j
    latjcl
    syl3anc
    @17
    @0
    @9
    @31
    @34
    @35
    @39
    @38
    cA
    cP
    @18
    c.or
    cK
    c.le
    cdlemk5.l
    cdlemk5.j
    cdlemk5.a
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
    @24
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    atmod2i1
    syl131anc
    @17
    @29
    @27
    @19
    c.an
    @17
    @29
    @20
    @6
    @18
    c.or
    co
    #
    c.or
    co
    #
    @27
    @17
    @29
    cP
    @6
    c.or
    co
    #
    @18
    c.or
    co
    #
    @20
    @6
    c.or
    co
    #
    @18
    c.or
    co
    #
    @55
    @17
    @41
    @45
    @18
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    @29
    @57
    wceq
    @44
    @47
    @17
    @31
    @60
    @38
    cA
    cB
    @18
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    #
    @17
    @2
    @4
    @61
    @36
    @46
    cB
    cR
    cT
    cN
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcl
    syl2anc
    #
    cB
    c.or
    cK
    cP
    @18
    @6
    cdlemk5.b
    cdlemk5.j
    latj32
    syl13anc
    @17
    @56
    @58
    @18
    c.or
    @17
    @2
    @4
    @11
    @56
    @58
    wceq
    @36
    @46
    @2
    @8
    @11
    @15
    simp3l
    cA
    cP
    cR
    cT
    cN
    cH
    c.or
    cK
    c.le
    cW
    cdlemk5.l
    cdlemk5.j
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trljat3
    syl3anc
    oveq1d
    @17
    @41
    @42
    @61
    @60
    @59
    @55
    wceq
    @44
    @48
    @63
    @62
    cB
    c.or
    cK
    @20
    @6
    @18
    cdlemk5.b
    cdlemk5.j
    latjass
    syl13anc
    3eqtrd
    @17
    @27
    @20
    @23
    @18
    c.or
    co
    #
    c.or
    co
    #
    @55
    @17
    @41
    @42
    @43
    @60
    @27
    @65
    wceq
    @44
    @48
    @53
    @62
    cB
    c.or
    cK
    @20
    @23
    @18
    cdlemk5.b
    cdlemk5.j
    latjass
    syl13anc
    @17
    @54
    @64
    @20
    c.or
    @17
    @54
    @18
    @21
    cR
    cfv
    #
    c.or
    co
    #
    @18
    @23
    c.or
    co
    #
    @64
    @17
    @54
    @18
    @6
    c.or
    co
    #
    @67
    @17
    @41
    @61
    @60
    @54
    @69
    wceq
    @44
    @63
    @62
    cB
    c.or
    cK
    @6
    @18
    cdlemk5.b
    cdlemk5.j
    latjcom
    syl3anc
    @17
    @66
    @6
    @18
    c.or
    @17
    @66
    @5
    @6
    @17
    @2
    @3
    @66
    @5
    wceq
    @36
    @51
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcnv
    syl2anc
    @2
    @3
    @4
    @7
    @16
    simp23
    eqtrd
    oveq2d
    eqtr4d
    @17
    @2
    @13
    @50
    @68
    @67
    wceq
    @36
    @37
    @52
    cR
    cT
    @12
    @21
    cH
    c.or
    cK
    cW
    cdlemk5.j
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trljco
    syl3anc
    @17
    @41
    @60
    @43
    @68
    @64
    wceq
    @44
    @62
    @53
    cB
    c.or
    cK
    @18
    @23
    cdlemk5.b
    cdlemk5.j
    latjcom
    syl3anc
    3eqtr2d
    oveq2d
    eqtr4d
    eqtr4d
    oveq2d
    @17
    @41
    @32
    @61
    @30
    @19
    wceq
    @44
    @40
    @63
    cB
    c.or
    cK
    c.an
    @19
    @6
    cdlemk5.b
    cdlemk5.j
    cdlemk5.m
    latabs2
    syl3anc
    3eqtr2d
    syl5eq
end
