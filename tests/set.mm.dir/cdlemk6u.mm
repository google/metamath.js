include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "cdlemk5u.mm"
include "wi.mm"
include "simp11l.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp212.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "simp213.mm"
include "simp1.mm"
include "simp211.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3l1.mm"
include "simp3l2.mm"
include "simp3r1.mm"
include "cdlemkoatnle.mm"
include "simpld.mm"
include "syl133anc.mm"
include "simp13.mm"
include "simp3r2.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "simp3r3.mm"
include "dalaw.mm"
include "mpd.mm"

theorem cdlemk6u
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  assume cdlemk1.b: |- B = ( Base ` K )
  assume cdlemk1.l: |- .<_ = ( le ` K )
  assume cdlemk1.j: |- .\/ = ( join ` K )
  assume cdlemk1.m: |- ./\ = ( meet ` K )
  assume cdlemk1.a: |- A = ( Atoms ` K )
  assume cdlemk1.h: |- H = ( LHyp ` K )
  assume cdlemk1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk1.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk1.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk1.o: |- O = ( S ` D )

  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint D f
  disjoint D i
  disjoint F f
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P f
  disjoint P i
  disjoint R f
  disjoint R i
  disjoint T f
  disjoint T i
  disjoint W f
  disjoint W i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ G e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` D ) /\ ( R ` X ) =/= ( R ` D ) ) ) ) -> ( ( P .\/ ( G ` P ) ) ./\ ( ( O ` P ) .\/ ( R ` ( G o. `' D ) ) ) ) .<_ ( ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' D ) ) .\/ ( R ` ( X o. `' D ) ) ) ) .\/ ( ( ( X ` P ) .\/ P ) ./\ ( ( R ` ( X o. `' D ) ) .\/ ( O ` P ) ) ) ) )

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
    cD
    cT
    wcel
    #
    w3a
    #
    cN
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    #
    w3a
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cD
    @16
    wne
    #
    cG
    @16
    wne
    #
    w3a
    #
    cD
    cR
    cfv
    #
    @13
    wne
    #
    cG
    cR
    cfv
    @21
    wne
    #
    cX
    cR
    cfv
    @21
    wne
    #
    w3a
    #
    wa
    #
    w3a
    #
    cP
    cP
    cO
    cfv
    #
    c.or
    co
    cP
    cG
    cfv
    #
    cG
    cD
    ccnv
    #
    ccom
    cR
    cfv
    #
    c.or
    co
    c.an
    co
    cP
    cX
    cfv
    #
    cX
    @30
    ccom
    cR
    cfv
    #
    c.or
    co
    c.le
    wbr
    #
    cP
    @29
    c.or
    co
    @28
    @31
    c.or
    co
    c.an
    co
    @29
    @32
    c.or
    co
    @31
    @33
    c.or
    co
    c.an
    co
    @32
    cP
    c.or
    co
    @33
    @28
    c.or
    co
    c.an
    co
    c.or
    co
    c.le
    wbr
    #
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cX
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemk5u
    @27
    @0
    @10
    @29
    cA
    wcel
    #
    @32
    cA
    wcel
    #
    @28
    cA
    wcel
    #
    @31
    cA
    wcel
    #
    @33
    cA
    wcel
    #
    @34
    @35
    wi
    @0
    @1
    @3
    @4
    @15
    @26
    simp11l
    @10
    @11
    @9
    @14
    @5
    @26
    simp22l
    #
    @27
    @2
    @7
    @10
    @36
    @2
    @3
    @4
    @15
    @26
    simp11
    #
    @6
    @7
    @8
    @12
    @14
    @5
    @26
    simp212
    #
    @41
    cA
    cP
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnat
    syl3anc
    @27
    @2
    @8
    @10
    @37
    @42
    @6
    @7
    @8
    @12
    @14
    @5
    @26
    simp213
    #
    @41
    cA
    cP
    cT
    cX
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnat
    syl3anc
    @27
    @5
    @6
    @12
    @14
    @17
    @18
    @22
    @38
    @5
    @15
    @26
    simp1
    @6
    @7
    @8
    @12
    @14
    @5
    @26
    simp211
    @5
    @9
    @12
    @14
    @26
    simp22
    @5
    @9
    @12
    @14
    @26
    simp23
    @17
    @18
    @19
    @25
    @5
    @15
    simp3l1
    @17
    @18
    @19
    @25
    @5
    @15
    simp3l2
    @22
    @23
    @24
    @20
    @5
    @15
    simp3r1
    @5
    @6
    @12
    @14
    w3a
    @17
    @18
    @22
    w3a
    w3a
    @38
    @28
    cW
    c.le
    wbr
    wn
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemkoatnle
    simpld
    syl133anc
    @27
    @2
    @7
    @4
    @23
    @39
    @42
    @43
    @2
    @3
    @4
    @15
    @26
    simp13
    #
    @22
    @23
    @24
    @20
    @5
    @15
    simp3r2
    cA
    cR
    cT
    cG
    cD
    cH
    cK
    cW
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl121anc
    @27
    @2
    @8
    @4
    @24
    @40
    @42
    @44
    @45
    @22
    @23
    @24
    @20
    @5
    @15
    simp3r3
    cA
    cR
    cT
    cX
    cD
    cH
    cK
    cW
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl121anc
    cA
    cP
    @29
    @32
    @28
    @31
    @33
    c.or
    cK
    c.le
    c.an
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    dalaw
    syl133anc
    mpd
end
