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
include "clat.mm"
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
include "simp31.mm"
include "simp32.mm"
include "jca.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simp22l.mm"
include "ltrnat.mm"
include "atbase.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latjcl.mm"
include "latmcl.mm"
include "simp11r.mm"
include "trlnidat.mm"
include "syl211anc.mm"
include "hlatjcl.mm"
include "simp13l.mm"
include "simp13r.mm"
include "cdlemk50.mm"
include "syld3an3.mm"
include "cdlemk51.mm"
include "lattrd.mm"
include "cdlemk47.mm"
include "breqtrrd.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "simp33.mm"
include "trlconid.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem cdlemk52
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` I ) ) ) -> ( ( [_ G / g ]_ X o. [_ I / g ]_ X ) ` P ) = ( [_ ( G o. I ) / g ]_ X ` P ) )

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
    c.le
    wbr
    #
    @25
    @28
    wceq
    #
    @21
    @25
    cP
    @22
    cfv
    #
    @18
    c.or
    co
    #
    cP
    @23
    cfv
    #
    @17
    c.or
    co
    #
    c.an
    co
    #
    @28
    c.le
    @21
    cB
    cK
    c.le
    @25
    @31
    @23
    cR
    cfv
    #
    c.or
    co
    #
    @33
    @22
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    @35
    cdlemk5.b
    cdlemk5.l
    @21
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @4
    @7
    @14
    @20
    simp11l
    #
    cK
    hllat
    syl
    #
    @21
    @25
    cA
    wcel
    #
    @25
    cB
    wcel
    @21
    @2
    @24
    cT
    wcel
    #
    @10
    @44
    @2
    @4
    @7
    @14
    @20
    simp11
    #
    @21
    @2
    @22
    cT
    wcel
    #
    @23
    cT
    wcel
    #
    @45
    @46
    @21
    @2
    @4
    @7
    @9
    @12
    @13
    @47
    @46
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
    #
    @21
    @2
    @4
    @15
    @16
    wa
    #
    @9
    @12
    @13
    @48
    @46
    @49
    @21
    @15
    @16
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
    jca
    #
    @50
    @51
    @52
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
    @22
    @23
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl3anc
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
    @24
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
    cB
    @25
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    @21
    @41
    @37
    cB
    wcel
    #
    @39
    cB
    wcel
    #
    @40
    cB
    wcel
    @43
    @21
    @41
    @31
    cB
    wcel
    #
    @36
    cB
    wcel
    #
    @61
    @43
    @21
    @31
    cA
    wcel
    #
    @63
    @21
    @2
    @47
    @10
    @65
    @46
    @53
    @59
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
    ltrnat
    syl3anc
    #
    cA
    cB
    @31
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    @21
    @2
    @48
    @64
    @46
    @58
    cB
    cR
    cT
    @23
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
    @31
    @36
    cdlemk5.b
    cdlemk5.j
    latjcl
    syl3anc
    @21
    @41
    @33
    cB
    wcel
    #
    @38
    cB
    wcel
    #
    @62
    @43
    @21
    @33
    cA
    wcel
    #
    @67
    @21
    @2
    @48
    @10
    @69
    @46
    @58
    @59
    cA
    cP
    cT
    @23
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
    cB
    @33
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    @21
    @2
    @47
    @68
    @46
    @53
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
    cB
    c.or
    cK
    @33
    @38
    cdlemk5.b
    cdlemk5.j
    latjcl
    syl3anc
    cB
    cK
    c.an
    @37
    @39
    cdlemk5.b
    cdlemk5.m
    latmcl
    syl3anc
    @21
    @41
    @32
    cB
    wcel
    #
    @34
    cB
    wcel
    #
    @35
    cB
    wcel
    @43
    @21
    @0
    @65
    @18
    cA
    wcel
    #
    @71
    @42
    @66
    @21
    @0
    @1
    @15
    @16
    @73
    @42
    @0
    @1
    @4
    @7
    @14
    @20
    simp11r
    #
    @55
    @56
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
    syl211anc
    cA
    cB
    c.or
    cK
    @31
    @18
    cdlemk5.b
    cdlemk5.j
    cdlemk5.a
    hlatjcl
    syl3anc
    @21
    @0
    @69
    @17
    cA
    wcel
    #
    @72
    @42
    @70
    @21
    @0
    @1
    @5
    @6
    @75
    @42
    @74
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
    syl211anc
    cA
    cB
    c.or
    cK
    @33
    @17
    cdlemk5.b
    cdlemk5.j
    cdlemk5.a
    hlatjcl
    syl3anc
    cB
    cK
    c.an
    @32
    @34
    cdlemk5.b
    cdlemk5.m
    latmcl
    syl3anc
    @8
    @14
    @20
    @54
    @25
    @40
    c.le
    wbr
    @57
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
    cdlemk50
    syld3an3
    @8
    @14
    @20
    @54
    @40
    @35
    c.le
    wbr
    @57
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
    cdlemk51
    syld3an3
    lattrd
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
    cdlemk47
    breqtrrd
    @21
    cK
    cal
    wcel
    #
    @44
    @28
    cA
    wcel
    #
    @29
    @30
    wb
    @21
    @0
    @77
    @42
    cK
    hlatl
    syl
    @60
    @21
    @2
    @27
    cT
    wcel
    #
    @10
    @78
    @46
    @21
    @2
    @4
    @26
    cT
    wcel
    #
    @26
    @3
    wne
    #
    wa
    @9
    @12
    @13
    @79
    @46
    @49
    @21
    @80
    @81
    @21
    @2
    @5
    @15
    @80
    @46
    @76
    @55
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
    @81
    @46
    @21
    @5
    @15
    @76
    @55
    jca
    @8
    @14
    @15
    @16
    @19
    simp33
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
    jca
    @50
    @51
    @52
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    @26
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
    @59
    cA
    cP
    cT
    @27
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
    @25
    @28
    cK
    c.le
    cdlemk5.l
    cdlemk5.a
    atcmp
    syl3anc
    mpbid
end
