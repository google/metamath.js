include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "cdlemk36.mm"
include "ccnv.mm"
include "ccom.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp13l.mm"
include "simp13r.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "hlatjcl.mm"
include "simp3l.mm"
include "simp3r1.mm"
include "simp21.mm"
include "ltrnat.mm"
include "atbase.mm"
include "simp12l.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "ltrnco.mm"
include "trlcl.mm"
include "latjcl.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latmle1.mm"
include "syl5eqbr.mm"
include "eqbrtrd.mm"

theorem cdlemk37
  let vz: setvar z
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
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  assume cdlemk4.b: |- B = ( Base ` K )
  assume cdlemk4.l: |- .<_ = ( le ` K )
  assume cdlemk4.j: |- .\/ = ( join ` K )
  assume cdlemk4.m: |- ./\ = ( meet ` K )
  assume cdlemk4.a: |- A = ( Atoms ` K )
  assume cdlemk4.h: |- H = ( LHyp ` K )
  assume cdlemk4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk4.z: |- Z = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) )
  assume cdlemk4.y: |- Y = ( ( P .\/ ( R ` G ) ) ./\ ( Z .\/ ( R ` ( G o. `' b ) ) ) )
  assume cdlemk4.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> ( z ` P ) = Y ) )

  disjoint b z
  disjoint ./\ b
  disjoint ./\ z
  disjoint .<_ b
  disjoint .<_ z
  disjoint .\/ b
  disjoint .\/ z
  disjoint A b
  disjoint A z
  disjoint B b
  disjoint B z
  disjoint F b
  disjoint F z
  disjoint G b
  disjoint G z
  disjoint H b
  disjoint H z
  disjoint K b
  disjoint K z
  disjoint N b
  disjoint N z
  disjoint P b
  disjoint P z
  disjoint R b
  disjoint R z
  disjoint T b
  disjoint T z
  disjoint W b
  disjoint W z
  disjoint Y z
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b i
  disjoint b j
  disjoint d e
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint d z
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint e j
  disjoint e z
  disjoint ./\ e
  disjoint f i
  disjoint f j
  disjoint f z
  disjoint ./\ f
  disjoint i j
  disjoint i z
  disjoint ./\ i
  disjoint j z
  disjoint ./\ j
  disjoint .<_ e
  disjoint .<_ i
  disjoint .<_ j
  disjoint .\/ d
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint .\/ j
  disjoint A i
  disjoint A j
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint G d
  disjoint G e
  disjoint G f
  disjoint G i
  disjoint G j
  disjoint H i
  disjoint H j
  disjoint K i
  disjoint K j
  disjoint N d
  disjoint N e
  disjoint N f
  disjoint N i
  disjoint N j
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint P j
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint T j
  disjoint W d
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint W j
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) ) ) -> ( X ` P ) .<_ ( P .\/ ( R ` G ) ) )

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
    wa
    #
    cG
    cT
    wcel
    #
    cG
    @4
    wne
    #
    wa
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
    vb
    cv
    #
    cT
    wcel
    #
    @18
    @4
    wne
    #
    @18
    cR
    cfv
    #
    @15
    wne
    #
    @21
    cG
    cR
    cfv
    #
    wne
    #
    w3a
    #
    wa
    #
    w3a
    #
    cP
    cX
    cfv
    cY
    cP
    @23
    c.or
    co
    #
    c.le
    vz
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
    cN
    cW
    cX
    cY
    cZ
    vb
    cdlemk4.b
    cdlemk4.l
    cdlemk4.j
    cdlemk4.m
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    cdlemk4.z
    cdlemk4.y
    cdlemk4.x
    cdlemk36
    @27
    cY
    @28
    cZ
    cG
    @18
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
    @28
    c.le
    cdlemk4.y
    @27
    cK
    clat
    wcel
    #
    @28
    cB
    wcel
    #
    @32
    cB
    wcel
    #
    @33
    @28
    c.le
    wbr
    @27
    @0
    @34
    @0
    @1
    @6
    @9
    @17
    @26
    simp11l
    #
    cK
    hllat
    syl
    #
    @27
    @0
    @12
    @23
    cA
    wcel
    #
    @35
    @37
    @12
    @13
    @11
    @16
    @10
    @26
    simp22l
    #
    @27
    @2
    @7
    @8
    @39
    @2
    @6
    @9
    @17
    @26
    simp11
    #
    @7
    @8
    @2
    @6
    @17
    @26
    simp13l
    #
    @7
    @8
    @2
    @6
    @17
    @26
    simp13r
    cA
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemk4.b
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    trlnidat
    syl3anc
    cA
    cB
    c.or
    cK
    cP
    @23
    cdlemk4.b
    cdlemk4.j
    cdlemk4.a
    hlatjcl
    syl3anc
    @27
    @34
    cZ
    cB
    wcel
    @31
    cB
    wcel
    #
    @36
    @38
    @27
    cZ
    cP
    @21
    c.or
    co
    #
    cP
    cN
    cfv
    #
    @18
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
    cB
    cdlemk4.z
    @27
    @34
    @44
    cB
    wcel
    #
    @49
    cB
    wcel
    #
    @50
    cB
    wcel
    @38
    @27
    @0
    @12
    @21
    cA
    wcel
    #
    @51
    @37
    @40
    @27
    @2
    @19
    @20
    @53
    @41
    @10
    @17
    @19
    @25
    simp3l
    #
    @20
    @22
    @24
    @19
    @10
    @17
    simp3r1
    cA
    cB
    cR
    cT
    @18
    cH
    cK
    cW
    cdlemk4.b
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    trlnidat
    syl3anc
    cA
    cB
    c.or
    cK
    cP
    @21
    cdlemk4.b
    cdlemk4.j
    cdlemk4.a
    hlatjcl
    syl3anc
    @27
    @34
    @45
    cB
    wcel
    #
    @48
    cB
    wcel
    #
    @52
    @38
    @27
    @45
    cA
    wcel
    #
    @55
    @27
    @2
    @11
    @12
    @57
    @41
    @10
    @11
    @14
    @16
    @26
    simp21
    @40
    cA
    cP
    cT
    cN
    cH
    cK
    c.le
    cW
    cdlemk4.l
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    ltrnat
    syl3anc
    cA
    cB
    @45
    cK
    cdlemk4.b
    cdlemk4.a
    atbase
    syl
    @27
    @2
    @47
    cT
    wcel
    #
    @56
    @41
    @27
    @2
    @19
    @46
    cT
    wcel
    #
    @58
    @41
    @54
    @27
    @2
    @3
    @59
    @41
    @3
    @5
    @2
    @9
    @17
    @26
    simp12l
    cT
    cF
    cH
    cK
    cW
    cdlemk4.h
    cdlemk4.t
    ltrncnv
    syl2anc
    cT
    @18
    @46
    cH
    cK
    cW
    cdlemk4.h
    cdlemk4.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @47
    cH
    cK
    cW
    cdlemk4.b
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    @45
    @48
    cdlemk4.b
    cdlemk4.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    @44
    @49
    cdlemk4.b
    cdlemk4.m
    latmcl
    syl3anc
    syl5eqel
    @27
    @2
    @30
    cT
    wcel
    #
    @43
    @41
    @27
    @2
    @7
    @29
    cT
    wcel
    #
    @60
    @41
    @42
    @27
    @2
    @19
    @61
    @41
    @54
    cT
    @18
    cH
    cK
    cW
    cdlemk4.h
    cdlemk4.t
    ltrncnv
    syl2anc
    cT
    cG
    @29
    cH
    cK
    cW
    cdlemk4.h
    cdlemk4.t
    ltrnco
    syl3anc
    cB
    cR
    cT
    @30
    cH
    cK
    cW
    cdlemk4.b
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    cZ
    @31
    cdlemk4.b
    cdlemk4.j
    latjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @28
    @32
    cdlemk4.b
    cdlemk4.l
    cdlemk4.m
    latmle1
    syl3anc
    syl5eqbr
    eqbrtrd
end
