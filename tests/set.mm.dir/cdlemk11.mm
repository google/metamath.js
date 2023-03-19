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
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp22.mm"
include "simp23.mm"
include "simp311.mm"
include "simp312.mm"
include "simp32.mm"
include "cdlemksat.mm"
include "syl133anc.mm"
include "atbase.mm"
include "simp11.mm"
include "simp12.mm"
include "simp21r.mm"
include "simp313.mm"
include "simp33.mm"
include "syl333anc.mm"
include "simp11r.mm"
include "simp13.mm"
include "simp22l.mm"
include "cdlemkvcl.mm"
include "syl231anc.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "trlcl.mm"
include "cdlemk7.mm"
include "cdlemk10.mm"
include "wi.mm"
include "latjlej2.mm"
include "syl13anc.mm"
include "mpd.mm"
include "lattrd.mm"

theorem cdlemk11
  let cA: class A
  let cB: class B
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
  assume cdlemk.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk.v: |- V = ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' F ) ) .\/ ( R ` ( X o. `' F ) ) ) )

  disjoint ./\ f
  disjoint .\/ f
  disjoint F f
  disjoint f i
  disjoint G f
  disjoint G i
  disjoint N f
  disjoint P f
  disjoint R f
  disjoint T f
  disjoint W f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ i
  disjoint A i
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N i
  disjoint P i
  disjoint R i
  disjoint T i
  disjoint W i
  disjoint X f
  disjoint X i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( ( N e. T /\ X e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ X =/= ( _I |` B ) ) /\ ( R ` G ) =/= ( R ` F ) /\ ( R ` X ) =/= ( R ` F ) ) ) -> ( ( S ` G ) ` P ) .<_ ( ( ( S ` X ) ` P ) .\/ ( R ` ( X o. `' G ) ) ) )

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
    cN
    cT
    wcel
    #
    cX
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
    cG
    @15
    wne
    #
    cX
    @15
    wne
    #
    w3a
    #
    cG
    cR
    cfv
    @12
    wne
    #
    cX
    cR
    cfv
    @12
    wne
    #
    w3a
    #
    w3a
    #
    cB
    cK
    c.le
    cP
    cG
    cS
    cfv
    cfv
    #
    cP
    cX
    cS
    cfv
    cfv
    #
    cV
    c.or
    co
    #
    @25
    cX
    cG
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
    cdlemk.b
    cdlemk.l
    @23
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @3
    @4
    @14
    @22
    simp11l
    #
    cK
    hllat
    syl
    #
    @23
    @24
    cA
    wcel
    #
    @24
    cB
    wcel
    @23
    @5
    @6
    @11
    @13
    @16
    @17
    @20
    @34
    @5
    @14
    @22
    simp1
    @6
    @7
    @11
    @13
    @5
    @22
    simp21l
    #
    @5
    @8
    @11
    @13
    @22
    simp22
    #
    @5
    @8
    @11
    @13
    @22
    simp23
    #
    @16
    @17
    @18
    @20
    @21
    @5
    @14
    simp311
    #
    @16
    @17
    @18
    @20
    @21
    @5
    @14
    simp312
    @5
    @14
    @19
    @20
    @21
    simp32
    cA
    cB
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
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk.s
    cdlemksat
    syl133anc
    cA
    cB
    @24
    cK
    cdlemk.b
    cdlemk.a
    atbase
    syl
    @23
    @31
    @25
    cB
    wcel
    #
    cV
    cB
    wcel
    #
    @26
    cB
    wcel
    @33
    @23
    @25
    cA
    wcel
    #
    @39
    @23
    @2
    @3
    @7
    @6
    @11
    @13
    @16
    @18
    @21
    @41
    @2
    @3
    @4
    @14
    @22
    simp11
    #
    @2
    @3
    @4
    @14
    @22
    simp12
    #
    @6
    @7
    @11
    @13
    @5
    @22
    simp21r
    #
    @35
    @36
    @37
    @38
    @16
    @17
    @18
    @20
    @21
    @5
    @14
    simp313
    @5
    @14
    @19
    @20
    @21
    simp33
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cX
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk.b
    cdlemk.l
    cdlemk.j
    cdlemk.a
    cdlemk.h
    cdlemk.t
    cdlemk.r
    cdlemk.m
    cdlemk.s
    cdlemksat
    syl333anc
    cA
    cB
    @25
    cK
    cdlemk.b
    cdlemk.a
    atbase
    syl
    #
    @23
    @0
    @1
    @3
    @4
    @7
    @9
    @40
    @32
    @0
    @1
    @3
    @4
    @14
    @22
    simp11r
    #
    @43
    @2
    @3
    @4
    @14
    @22
    simp13
    #
    @44
    @9
    @10
    @8
    @13
    @5
    @22
    simp22l
    cA
    cB
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
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
    cdlemk.v
    cdlemkvcl
    syl231anc
    #
    cB
    c.or
    cK
    @25
    cV
    cdlemk.b
    cdlemk.j
    latjcl
    syl3anc
    @23
    @31
    @39
    @29
    cB
    wcel
    #
    @30
    cB
    wcel
    @33
    @45
    @23
    @2
    @28
    cT
    wcel
    #
    @49
    @42
    @23
    @2
    @7
    @27
    cT
    wcel
    #
    @50
    @42
    @44
    @23
    @2
    @4
    @51
    @42
    @47
    cT
    cG
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrncnv
    syl2anc
    cT
    cX
    @27
    cH
    cK
    cW
    cdlemk.h
    cdlemk.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @28
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
    cB
    c.or
    cK
    @25
    @29
    cdlemk.b
    cdlemk.j
    latjcl
    syl3anc
    cA
    cB
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
    cV
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
    cdlemk.s
    cdlemk.v
    cdlemk7
    @23
    cV
    @29
    c.le
    wbr
    #
    @26
    @30
    c.le
    wbr
    #
    @23
    @0
    @1
    @3
    @4
    @7
    @11
    @53
    @32
    @46
    @43
    @47
    @44
    @36
    cA
    cB
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cV
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
    cdlemk.v
    cdlemk10
    syl231anc
    @23
    @31
    @40
    @49
    @39
    @53
    @54
    wi
    @33
    @48
    @52
    @45
    cB
    c.or
    cK
    c.le
    cV
    @29
    @25
    cdlemk.b
    cdlemk.l
    cdlemk.j
    latjlej2
    syl13anc
    mpd
    lattrd
end
