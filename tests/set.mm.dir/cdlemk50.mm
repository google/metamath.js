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
include "csb.mm"
include "ccom.mm"
include "co.mm"
include "cdlemk49.mm"
include "cdlemk48.mm"
include "clat.mm"
include "wb.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "cdlemk35s.mm"
include "syl132anc.mm"
include "simp3.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simp22l.mm"
include "ltrnat.mm"
include "atbase.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"

theorem cdlemk50
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
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
  assume cdlemk5.b: |- B = ( Base ` K )
  assume cdlemk5.l: |- .<_ = ( le ` K )
  assume cdlemk5.j: |- .\/ = ( join ` K )
  assume cdlemk5.m: |- ./\ = ( meet ` K )
  assume cdlemk5.a: |- A = ( Atoms ` K )
  assume cdlemk5.h: |- H = ( LHyp ` K )
  assume cdlemk5.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk5.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk5.z: |- Z = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) )
  assume cdlemk5.y: |- Y = ( ( P .\/ ( R ` g ) ) ./\ ( Z .\/ ( R ` ( g o. `' b ) ) ) )
  assume cdlemk5.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` g ) ) -> ( z ` P ) = Y ) )

  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint G g
  disjoint b z
  disjoint ./\ b
  disjoint ./\ z
  disjoint .<_ b
  disjoint g z
  disjoint .<_ g
  disjoint .<_ z
  disjoint .\/ b
  disjoint .\/ z
  disjoint A b
  disjoint A g
  disjoint A z
  disjoint B b
  disjoint B z
  disjoint F b
  disjoint F g
  disjoint F z
  disjoint G z
  disjoint H b
  disjoint H g
  disjoint H z
  disjoint K b
  disjoint K g
  disjoint K z
  disjoint N b
  disjoint N g
  disjoint N z
  disjoint P b
  disjoint P z
  disjoint R b
  disjoint R z
  disjoint T b
  disjoint T z
  disjoint W b
  disjoint W g
  disjoint W z
  disjoint Y z
  disjoint G b
  disjoint I b
  disjoint I g
  disjoint I z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) ) ) -> ( ( [_ G / g ]_ X o. [_ I / g ]_ X ) ` P ) .<_ ( ( ( [_ G / g ]_ X ` P ) .\/ ( R ` [_ I / g ]_ X ) ) ./\ ( ( [_ I / g ]_ X ` P ) .\/ ( R ` [_ G / g ]_ X ) ) ) )

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
    cG
    @3
    wne
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
    cN
    cR
    cfv
    wceq
    #
    w3a
    #
    cI
    cT
    wcel
    cI
    @3
    wne
    wa
    #
    w3a
    #
    cP
    vg
    cG
    cX
    csb
    #
    vg
    cI
    cX
    csb
    #
    ccom
    #
    cfv
    #
    cP
    @15
    cfv
    #
    @16
    cR
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    @18
    cP
    @16
    cfv
    #
    @15
    cR
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    @18
    @21
    @25
    c.an
    co
    c.le
    wbr
    #
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    cG
    cH
    cI
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
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5.z
    cdlemk5.y
    cdlemk5.x
    cdlemk49
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    cG
    cH
    cI
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
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5.z
    cdlemk5.y
    cdlemk5.x
    cdlemk48
    @14
    cK
    clat
    wcel
    #
    @18
    cB
    wcel
    #
    @21
    cB
    wcel
    #
    @25
    cB
    wcel
    #
    @22
    @26
    wa
    @27
    wb
    @14
    @0
    @28
    @0
    @1
    @4
    @5
    @12
    @13
    simp11l
    cK
    hllat
    syl
    #
    @14
    @18
    cA
    wcel
    #
    @29
    @14
    @2
    @17
    cT
    wcel
    #
    @8
    @33
    @2
    @4
    @5
    @12
    @13
    simp11
    #
    @14
    @2
    @15
    cT
    wcel
    #
    @16
    cT
    wcel
    #
    @34
    @35
    @14
    @2
    @4
    @5
    @7
    @10
    @11
    @36
    @35
    @2
    @4
    @5
    @12
    @13
    simp12
    #
    @2
    @4
    @5
    @12
    @13
    simp13
    @6
    @7
    @10
    @11
    @13
    simp21
    #
    @6
    @7
    @10
    @11
    @13
    simp22
    #
    @6
    @7
    @10
    @11
    @13
    simp23
    #
    vz
    cA
    cB
    cP
    cR
    cT
    vg
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
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5.z
    cdlemk5.y
    cdlemk5.x
    cdlemk35s
    syl132anc
    #
    @14
    @2
    @4
    @13
    @7
    @10
    @11
    @37
    @35
    @38
    @6
    @12
    @13
    simp3
    @39
    @40
    @41
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    cI
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
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5.z
    cdlemk5.y
    cdlemk5.x
    cdlemk35s
    syl132anc
    #
    cT
    @15
    @16
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl3anc
    @8
    @9
    @7
    @11
    @6
    @13
    simp22l
    #
    cA
    cP
    cT
    @17
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
    cA
    cB
    @18
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    @14
    @28
    @19
    cB
    wcel
    #
    @20
    cB
    wcel
    #
    @30
    @32
    @14
    @19
    cA
    wcel
    #
    @45
    @14
    @2
    @36
    @8
    @47
    @35
    @42
    @44
    cA
    cP
    cT
    @15
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
    cA
    cB
    @19
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    @14
    @2
    @37
    @46
    @35
    @43
    cB
    cR
    cT
    @16
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    @19
    @20
    cdlemk5.b
    cdlemk5.j
    latjcl
    syl3anc
    @14
    @28
    @23
    cB
    wcel
    #
    @24
    cB
    wcel
    #
    @31
    @32
    @14
    @23
    cA
    wcel
    #
    @48
    @14
    @2
    @37
    @8
    @50
    @35
    @43
    @44
    cA
    cP
    cT
    @16
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
    cA
    cB
    @23
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    @14
    @2
    @36
    @49
    @35
    @42
    cB
    cR
    cT
    @15
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcl
    syl2anc
    cB
    c.or
    cK
    @23
    @24
    cdlemk5.b
    cdlemk5.j
    latjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @18
    @21
    @25
    cdlemk5.b
    cdlemk5.l
    cdlemk5.m
    latlem12
    syl13anc
    mpbi2and
end
