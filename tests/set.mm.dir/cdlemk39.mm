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
include "co.mm"
include "simp1l.mm"
include "simp3ll.mm"
include "simp1.mm"
include "simp22l.mm"
include "simp22r.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "hlatlej1.mm"
include "cdlemk38.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "cdlemk35.mm"
include "ltrnat.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmlem1.mm"
include "mpd.mm"
include "simp3l.mm"
include "trlval2.mm"
include "trlval5.mm"
include "3brtr4d.mm"

theorem cdlemk39
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> ( R ` X ) .<_ ( R ` G ) )

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
    cF
    cid
    cB
    cres
    #
    wne
    wa
    #
    cG
    cT
    wcel
    #
    cG
    @3
    wne
    #
    wa
    cN
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
    cN
    cR
    cfv
    wceq
    #
    wa
    #
    w3a
    #
    cP
    cP
    cX
    cfv
    #
    c.or
    co
    #
    cW
    c.an
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
    cW
    c.an
    co
    #
    cX
    cR
    cfv
    #
    @18
    c.le
    @14
    @16
    @19
    c.le
    wbr
    #
    @17
    @20
    c.le
    wbr
    #
    @14
    cP
    @19
    c.le
    wbr
    #
    @15
    @19
    c.le
    wbr
    #
    @22
    @14
    @0
    @9
    @18
    cA
    wcel
    #
    @24
    @0
    @1
    @8
    @13
    simp1l
    #
    @9
    @10
    @12
    @2
    @8
    simp3ll
    #
    @14
    @2
    @5
    @6
    @26
    @2
    @8
    @13
    simp1
    #
    @5
    @6
    @4
    @7
    @2
    @13
    simp22l
    #
    @5
    @6
    @4
    @7
    @2
    @13
    simp22r
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
    #
    cA
    cP
    @18
    c.or
    cK
    c.le
    cdlemk4.l
    cdlemk4.j
    cdlemk4.a
    hlatlej1
    syl3anc
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
    cdlemk38
    @14
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @15
    cB
    wcel
    #
    @19
    cB
    wcel
    #
    @24
    @25
    wa
    @22
    wb
    @14
    @0
    @32
    @27
    cK
    hllat
    syl
    #
    @14
    @9
    @33
    @28
    cA
    cB
    cP
    cK
    cdlemk4.b
    cdlemk4.a
    atbase
    syl
    @14
    @15
    cA
    wcel
    #
    @34
    @14
    @2
    cX
    cT
    wcel
    #
    @9
    @37
    @29
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
    cdlemk35
    #
    @28
    cA
    cP
    cT
    cX
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
    #
    cA
    cB
    @15
    cK
    cdlemk4.b
    cdlemk4.a
    atbase
    syl
    @14
    @0
    @9
    @26
    @35
    @27
    @28
    @31
    cA
    cB
    c.or
    cK
    cP
    @18
    cdlemk4.b
    cdlemk4.j
    cdlemk4.a
    hlatjcl
    syl3anc
    #
    cB
    c.or
    cK
    c.le
    cP
    @15
    @19
    cdlemk4.b
    cdlemk4.l
    cdlemk4.j
    latjle12
    syl13anc
    mpbi2and
    @14
    @32
    @16
    cB
    wcel
    #
    @35
    cW
    cB
    wcel
    #
    @22
    @23
    wi
    @36
    @14
    @0
    @9
    @37
    @42
    @27
    @28
    @40
    cA
    cB
    c.or
    cK
    cP
    @15
    cdlemk4.b
    cdlemk4.j
    cdlemk4.a
    hlatjcl
    syl3anc
    @41
    @14
    @1
    @43
    @0
    @1
    @8
    @13
    simp1r
    cB
    cH
    cK
    cW
    cdlemk4.b
    cdlemk4.h
    lhpbase
    syl
    cB
    cK
    c.le
    c.an
    @16
    @19
    cW
    cdlemk4.b
    cdlemk4.l
    cdlemk4.m
    latmlem1
    syl13anc
    mpd
    @14
    @2
    @38
    @11
    @21
    @17
    wceq
    @29
    @39
    @2
    @8
    @11
    @12
    simp3l
    #
    cA
    cP
    cR
    cT
    cX
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemk4.l
    cdlemk4.j
    cdlemk4.m
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    trlval2
    syl3anc
    @14
    @2
    @5
    @11
    @18
    @20
    wceq
    @29
    @30
    @44
    cA
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
    cdlemk4.l
    cdlemk4.j
    cdlemk4.m
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    trlval5
    syl3anc
    3brtr4d
end
