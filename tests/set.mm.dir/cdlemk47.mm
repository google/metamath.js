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
include "simp11l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "cdlemk35s.mm"
include "syl132anc.mm"
include "ltrnel.mm"
include "syl3anc.mm"
include "simpld.mm"
include "simp31.mm"
include "simp32.mm"
include "trlnidat.mm"
include "jca.mm"
include "simp22l.mm"
include "ltrnat.mm"
include "simp13l.mm"
include "simp13r.mm"
include "ltrnco.mm"
include "simp33.mm"
include "trlconid.mm"
include "3jca.mm"
include "cdlemk46.mm"
include "syld3an3.mm"
include "cdlemk45.mm"
include "trlle.mm"
include "syl2anc.mm"
include "necomd.mm"
include "lhp2atne.mm"
include "syl321anc.mm"
include "2atm.mm"
include "syl333anc.mm"

theorem cdlemk47
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` I ) ) ) -> ( [_ ( G o. I ) / g ]_ X ` P ) = ( ( ( [_ G / g ]_ X ` P ) .\/ ( R ` I ) ) ./\ ( ( [_ I / g ]_ X ` P ) .\/ ( R ` G ) ) ) )

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
    #
    cI
    @3
    wne
    #
    cG
    cR
    cfv
    #
    cI
    cR
    cfv
    #
    wne
    #
    w3a
    #
    w3a
    #
    @0
    cP
    vg
    cG
    cX
    csb
    #
    cfv
    #
    cA
    wcel
    #
    @18
    cA
    wcel
    #
    cP
    vg
    cI
    cX
    csb
    #
    cfv
    #
    cA
    wcel
    #
    @17
    cA
    wcel
    #
    cP
    vg
    cG
    cI
    ccom
    #
    cX
    csb
    #
    cfv
    #
    cA
    wcel
    #
    @32
    @23
    @18
    c.or
    co
    #
    c.le
    wbr
    #
    @32
    @27
    @17
    c.or
    co
    #
    c.le
    wbr
    #
    @34
    @36
    wne
    #
    @32
    @34
    @36
    c.an
    co
    wceq
    @0
    @1
    @4
    @7
    @14
    @20
    simp11l
    @21
    @24
    @23
    cW
    c.le
    wbr
    wn
    #
    @21
    @2
    @22
    cT
    wcel
    #
    @12
    @24
    @39
    wa
    #
    @2
    @4
    @7
    @14
    @20
    simp11
    #
    @21
    @2
    @4
    @7
    @9
    @12
    @13
    @40
    @42
    @2
    @4
    @7
    @14
    @20
    simp12
    #
    @2
    @4
    @7
    @14
    @20
    simp13
    @8
    @9
    @12
    @13
    @20
    simp21
    #
    @8
    @9
    @12
    @13
    @20
    simp22
    #
    @8
    @9
    @12
    @13
    @20
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
    @45
    cA
    cP
    cT
    @22
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
    #
    simpld
    @21
    @2
    @15
    @16
    @25
    @42
    @8
    @14
    @15
    @16
    @19
    simp31
    #
    @8
    @14
    @15
    @16
    @19
    simp32
    #
    cA
    cB
    cR
    cT
    cI
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
    @21
    @2
    @26
    cT
    wcel
    #
    @10
    @28
    @42
    @21
    @2
    @4
    @15
    @16
    wa
    @9
    @12
    @13
    @51
    @42
    @43
    @21
    @15
    @16
    @48
    @49
    jca
    @44
    @45
    @46
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
    @10
    @11
    @9
    @13
    @8
    @20
    simp22l
    #
    cA
    cP
    cT
    @26
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
    @21
    @2
    @5
    @6
    @29
    @42
    @5
    @6
    @2
    @4
    @14
    @20
    simp13l
    #
    @5
    @6
    @2
    @4
    @14
    @20
    simp13r
    cA
    cB
    cR
    cT
    cG
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
    @21
    @2
    @31
    cT
    wcel
    #
    @10
    @33
    @42
    @21
    @2
    @4
    @30
    cT
    wcel
    #
    @30
    @3
    wne
    #
    wa
    @9
    @12
    @13
    @56
    @42
    @43
    @21
    @57
    @58
    @21
    @2
    @5
    @15
    @57
    @42
    @54
    @48
    cT
    cG
    cI
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl3anc
    @21
    @2
    @5
    @15
    wa
    @19
    @58
    @42
    @21
    @5
    @15
    @54
    @48
    jca
    @8
    @14
    @15
    @16
    @19
    simp33
    #
    cB
    cR
    cT
    cG
    cI
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlconid
    syl3anc
    #
    jca
    @44
    @45
    @46
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    @30
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
    @52
    cA
    cP
    cT
    @31
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
    @8
    @14
    @20
    @15
    @16
    @58
    w3a
    #
    @35
    @21
    @15
    @16
    @58
    @48
    @49
    @60
    3jca
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
    cdlemk46
    syld3an3
    @8
    @14
    @20
    @61
    @37
    @62
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
    cdlemk45
    syld3an3
    @21
    @2
    @41
    @28
    @25
    @18
    cW
    c.le
    wbr
    #
    wa
    @29
    @17
    cW
    c.le
    wbr
    #
    wa
    @18
    @17
    wne
    @38
    @42
    @47
    @53
    @21
    @25
    @63
    @50
    @21
    @2
    @15
    @63
    @42
    @48
    cR
    cT
    cI
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
    jca
    @21
    @29
    @64
    @55
    @21
    @2
    @5
    @64
    @42
    @54
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
    syl2anc
    jca
    @21
    @17
    @18
    @59
    necomd
    cA
    @23
    @27
    @18
    cH
    c.or
    cK
    c.le
    @17
    cW
    cdlemk5.l
    cdlemk5.j
    cdlemk5.a
    cdlemk5.h
    lhp2atne
    syl321anc
    cA
    @23
    @18
    @27
    @17
    @32
    c.or
    cK
    c.le
    c.an
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    2atm
    syl333anc
end
