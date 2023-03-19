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
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "cdlemk13.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp13.mm"
include "simp32.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "hlatjcl.mm"
include "simp21.mm"
include "ltrnat.mm"
include "simp12.mm"
include "simp33.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "latmle2.mm"
include "eqbrtrd.mm"
include "wi.mm"
include "fveq1i.mm"
include "cdlemksat.mm"
include "syl5eqel.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "trlle.mm"
include "cdlemkoatnle.mm"
include "simprd.mm"
include "nbrne2.mm"
include "necomd.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "mpd.mm"
include "trlcocnv.mm"
include "oveq2d.mm"
include "breqtrd.mm"

theorem cdlemk14
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
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ ( R ` D ) =/= ( R ` F ) ) ) -> ( N ` P ) .<_ ( ( O ` P ) .\/ ( R ` ( F o. `' D ) ) ) )

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
    @13
    wne
    #
    cD
    cR
    cfv
    #
    @10
    wne
    #
    w3a
    #
    w3a
    #
    cP
    cN
    cfv
    #
    cP
    cO
    cfv
    #
    cD
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
    @21
    cF
    cD
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    c.le
    @19
    @21
    @20
    @24
    c.or
    co
    #
    c.le
    wbr
    #
    @20
    @25
    c.le
    wbr
    #
    @19
    @21
    cP
    @16
    c.or
    co
    #
    @27
    c.an
    co
    #
    @27
    c.le
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
    cdlemk13
    @19
    cK
    clat
    wcel
    #
    @30
    cB
    wcel
    #
    @27
    cB
    wcel
    #
    @31
    @27
    c.le
    wbr
    @19
    @0
    @32
    @0
    @1
    @3
    @4
    @12
    @18
    simp11l
    #
    cK
    hllat
    syl
    @19
    @0
    @7
    @16
    cA
    wcel
    #
    @33
    @35
    @7
    @8
    @6
    @11
    @5
    @18
    simp22l
    #
    @19
    @2
    @4
    @15
    @36
    @2
    @3
    @4
    @12
    @18
    simp11
    #
    @2
    @3
    @4
    @12
    @18
    simp13
    #
    @5
    @12
    @14
    @15
    @17
    simp32
    cA
    cB
    cR
    cT
    cD
    cH
    cK
    cW
    cdlemk1.b
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlnidat
    syl3anc
    cA
    cB
    c.or
    cK
    cP
    @16
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    @19
    @0
    @20
    cA
    wcel
    #
    @24
    cA
    wcel
    #
    @34
    @35
    @19
    @2
    @6
    @7
    @40
    @38
    @5
    @6
    @9
    @11
    @18
    simp21
    @37
    cA
    cP
    cT
    cN
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
    #
    @19
    @2
    @4
    @3
    @17
    @41
    @38
    @39
    @2
    @3
    @4
    @12
    @18
    simp12
    #
    @5
    @12
    @14
    @15
    @17
    simp33
    cA
    cR
    cT
    cD
    cF
    cH
    cK
    cW
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl121anc
    #
    cA
    cB
    c.or
    cK
    @20
    @24
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @30
    @27
    cdlemk1.b
    cdlemk1.l
    cdlemk1.m
    latmle2
    syl3anc
    eqbrtrd
    @19
    @0
    @21
    cA
    wcel
    #
    @40
    @41
    @21
    @24
    wne
    @28
    @29
    wi
    @35
    @19
    @21
    cP
    cD
    cS
    cfv
    #
    cfv
    cA
    cP
    cO
    @46
    cdlemk1.o
    fveq1i
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cD
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.m
    cdlemk1.s
    cdlemksat
    syl5eqel
    @42
    @44
    @19
    @24
    @21
    @19
    @24
    cW
    c.le
    wbr
    #
    @21
    cW
    c.le
    wbr
    wn
    #
    @24
    @21
    wne
    @19
    @2
    @23
    cT
    wcel
    #
    @47
    @38
    @19
    @2
    @4
    @22
    cT
    wcel
    #
    @49
    @38
    @39
    @19
    @2
    @3
    @50
    @38
    @43
    cT
    cF
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    ltrncnv
    syl2anc
    cT
    cD
    @22
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    ltrnco
    syl3anc
    cR
    cT
    @23
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlle
    syl2anc
    @19
    @45
    @48
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
    simprd
    @24
    @21
    cW
    c.le
    nbrne2
    syl2anc
    necomd
    cA
    @21
    @20
    @24
    c.or
    cK
    c.le
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    hlatexch2
    syl131anc
    mpd
    @19
    @24
    @26
    @21
    c.or
    @19
    @2
    @4
    @3
    @24
    @26
    wceq
    @38
    @39
    @43
    cR
    cT
    cD
    cF
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnv
    syl3anc
    oveq2d
    breqtrd
end
