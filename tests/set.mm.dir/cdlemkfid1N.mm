include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "simp1.mm"
include "simp23.mm"
include "simp3r.mm"
include "trljat3.mm"
include "syl3anc.mm"
include "simp1l.mm"
include "simp21.mm"
include "simp3rl.mm"
include "ltrnat.mm"
include "hlatjcom.mm"
include "trlcoabs2N.mm"
include "syl121anc.mm"
include "trlcocnv.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "3eqtr4d.mm"
include "oveq12d.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "simp1r.mm"
include "simp3l.mm"
include "trlcocnvat.mm"
include "syl221anc.mm"
include "cp0.mm"
include "wo.mm"
include "ltrnel.mm"
include "ltrncnv.mm"
include "trlcnv.mm"
include "neeqtrrd.mm"
include "simp22.mm"
include "ltrncnvnid.mm"
include "trlcone.mm"
include "syl122anc.mm"
include "eqid.mm"
include "trlator0.mm"
include "trlle.mm"
include "syl21anc.mm"
include "ltrnco.mm"
include "lhp2at0nle.mm"
include "syl322anc.mm"
include "2llnma1b.mm"
include "syl131anc.mm"
include "eqtrd.mm"

theorem cdlemkfid1N
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
  assume cdlemk5.b: |- B = ( Base ` K )
  assume cdlemk5.l: |- .<_ = ( le ` K )
  assume cdlemk5.j: |- .\/ = ( join ` K )
  assume cdlemk5.m: |- ./\ = ( meet ` K )
  assume cdlemk5.a: |- A = ( Atoms ` K )
  assume cdlemk5.h: |- H = ( LHyp ` K )
  assume cdlemk5.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk5.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) /\ G e. T ) /\ ( ( R ` G ) =/= ( R ` F ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( P .\/ ( R ` G ) ) ./\ ( ( F ` P ) .\/ ( R ` ( G o. `' F ) ) ) ) = ( G ` P ) )

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
    cF
    cid
    cB
    cres
    #
    wne
    #
    cG
    cT
    wcel
    #
    w3a
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
    wa
    #
    w3a
    #
    cP
    @8
    c.or
    co
    #
    cP
    cF
    cfv
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
    c.or
    co
    #
    c.an
    co
    cP
    cG
    cfv
    #
    @8
    c.or
    co
    #
    @22
    @20
    c.or
    co
    #
    c.an
    co
    #
    @22
    @15
    @16
    @23
    @21
    @24
    c.an
    @15
    @2
    @6
    @13
    @16
    @23
    wceq
    @2
    @7
    @14
    simp1
    #
    @2
    @3
    @5
    @6
    @14
    simp23
    #
    @2
    @7
    @10
    @13
    simp3r
    #
    cA
    cP
    cR
    cT
    cG
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
    @15
    @17
    @22
    c.or
    co
    #
    @22
    @17
    c.or
    co
    #
    @21
    @24
    @15
    @0
    @17
    cA
    wcel
    #
    @22
    cA
    wcel
    #
    @29
    @30
    wceq
    @0
    @1
    @7
    @14
    simp1l
    #
    @15
    @2
    @3
    @11
    @31
    @26
    @2
    @3
    @5
    @6
    @14
    simp21
    #
    @11
    @12
    @10
    @2
    @7
    simp3rl
    #
    cA
    cP
    cT
    cF
    cH
    cK
    c.le
    cW
    cdlemk5.l
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    ltrnat
    syl3anc
    @15
    @2
    @6
    @11
    @32
    @26
    @27
    @35
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk5.l
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    ltrnat
    syl3anc
    #
    cA
    c.or
    cK
    @17
    @22
    cdlemk5.j
    cdlemk5.a
    hlatjcom
    syl3anc
    @15
    @2
    @3
    @6
    @13
    @21
    @29
    wceq
    @26
    @34
    @27
    @28
    cA
    cP
    cR
    cT
    cF
    cG
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
    trlcoabs2N
    syl121anc
    @15
    @22
    cF
    cG
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    @24
    @30
    @15
    @37
    @20
    @22
    c.or
    @15
    @2
    @3
    @6
    @37
    @20
    wceq
    @26
    @34
    @27
    cR
    cT
    cF
    cG
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcocnv
    syl3anc
    oveq2d
    @15
    @2
    @6
    @3
    @13
    @38
    @30
    wceq
    @26
    @27
    @34
    @28
    cA
    cP
    cR
    cT
    cG
    cF
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
    trlcoabs2N
    syl121anc
    eqtr3d
    3eqtr4d
    oveq12d
    @15
    @0
    @8
    cB
    wcel
    #
    @32
    @20
    cA
    wcel
    #
    @20
    @23
    c.le
    wbr
    wn
    #
    @25
    @22
    wceq
    @33
    @15
    @2
    @6
    @39
    @26
    @27
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcl
    syl2anc
    @36
    @15
    @0
    @1
    @6
    @3
    @10
    @40
    @33
    @0
    @1
    @7
    @14
    simp1r
    #
    @27
    @34
    @2
    @7
    @10
    @13
    simp3l
    #
    cA
    cR
    cT
    cG
    cF
    cH
    cK
    cW
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcocnvat
    syl221anc
    #
    @15
    @2
    @32
    @22
    cW
    c.le
    wbr
    wn
    wa
    #
    @8
    @20
    wne
    #
    @8
    cA
    wcel
    @8
    cK
    cp0
    cfv
    #
    wceq
    wo
    #
    @8
    cW
    c.le
    wbr
    #
    @40
    @20
    cW
    c.le
    wbr
    #
    @41
    @26
    @15
    @2
    @6
    @13
    @45
    @26
    @27
    @28
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk5.l
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    ltrnel
    syl3anc
    @15
    @2
    @6
    @18
    cT
    wcel
    #
    @8
    @18
    cR
    cfv
    #
    wne
    @18
    @4
    wne
    #
    @46
    @26
    @27
    @15
    @2
    @3
    @51
    @26
    @34
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
    @15
    @8
    @9
    @52
    @43
    @15
    @2
    @3
    @52
    @9
    wceq
    @26
    @34
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
    neeqtrrd
    @15
    @2
    @3
    @5
    @53
    @26
    @34
    @2
    @3
    @5
    @6
    @14
    simp22
    cB
    cT
    cF
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    ltrncnvnid
    syl3anc
    cB
    cR
    cT
    cG
    @18
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcone
    syl122anc
    @15
    @2
    @6
    @48
    @26
    @27
    cA
    cR
    cT
    cG
    cH
    cK
    cW
    @47
    @47
    eqid
    #
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlator0
    syl2anc
    @15
    @0
    @1
    @6
    @49
    @33
    @42
    @27
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk5.l
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlle
    syl21anc
    @44
    @15
    @2
    @19
    cT
    wcel
    #
    @50
    @26
    @15
    @2
    @6
    @51
    @56
    @26
    @27
    @54
    cT
    cG
    @18
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl3anc
    cR
    cT
    @19
    cH
    cK
    c.le
    cW
    cdlemk5.l
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlle
    syl2anc
    cA
    @22
    @8
    cH
    c.or
    cK
    c.le
    @20
    cW
    @47
    cdlemk5.l
    cdlemk5.j
    @55
    cdlemk5.a
    cdlemk5.h
    lhp2at0nle
    syl322anc
    cA
    cB
    @22
    @20
    c.or
    cK
    c.le
    c.an
    @8
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    2llnma1b
    syl131anc
    eqtrd
end
