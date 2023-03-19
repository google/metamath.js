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
include "co.mm"
include "simp11.mm"
include "simp12.mm"
include "simp3.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "cdlemk39s.mm"
include "syl132anc.mm"
include "clat.mm"
include "wi.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "cdlemk35s.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "simp3l.mm"
include "simp3r.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "atbase.mm"
include "simp13.mm"
include "simp22l.mm"
include "ltrnat.mm"
include "latjlej2.mm"
include "syl13anc.mm"
include "mpd.mm"
include "simp13l.mm"
include "simp13r.mm"
include "latjcl.mm"
include "hlatjcl.mm"
include "latmlem12.mm"
include "syl122anc.mm"
include "mp2and.mm"

theorem cdlemk51
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) ) ) -> ( ( ( [_ G / g ]_ X ` P ) .\/ ( R ` [_ I / g ]_ X ) ) ./\ ( ( [_ I / g ]_ X ` P ) .\/ ( R ` [_ G / g ]_ X ) ) ) .<_ ( ( ( [_ G / g ]_ X ` P ) .\/ ( R ` I ) ) ./\ ( ( [_ I / g ]_ X ` P ) .\/ ( R ` G ) ) ) )

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
    cfv
    #
    vg
    cI
    cX
    csb
    #
    cR
    cfv
    #
    c.or
    co
    #
    @20
    cI
    cR
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    cP
    @21
    cfv
    #
    @19
    cR
    cfv
    #
    c.or
    co
    #
    @27
    cG
    cR
    cfv
    #
    c.or
    co
    #
    c.le
    wbr
    #
    @23
    @29
    c.an
    co
    @25
    @31
    c.an
    co
    c.le
    wbr
    #
    @18
    @22
    @24
    c.le
    wbr
    #
    @26
    @18
    @2
    @4
    @17
    @9
    @12
    @13
    @34
    @2
    @4
    @7
    @14
    @17
    simp11
    #
    @2
    @4
    @7
    @14
    @17
    simp12
    #
    @8
    @14
    @17
    simp3
    #
    @8
    @9
    @12
    @13
    @17
    simp21
    #
    @8
    @9
    @12
    @13
    @17
    simp22
    #
    @8
    @9
    @12
    @13
    @17
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
    cdlemk39s
    syl132anc
    @18
    cK
    clat
    wcel
    #
    @22
    cB
    wcel
    #
    @24
    cB
    wcel
    #
    @20
    cB
    wcel
    #
    @34
    @26
    wi
    @18
    @0
    @41
    @0
    @1
    @4
    @7
    @14
    @17
    simp11l
    #
    cK
    hllat
    syl
    #
    @18
    @2
    @21
    cT
    wcel
    #
    @42
    @35
    @18
    @2
    @4
    @17
    @9
    @12
    @13
    @47
    @35
    @36
    @37
    @38
    @39
    @40
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
    cB
    cR
    cT
    @21
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
    @18
    @24
    cA
    wcel
    #
    @43
    @18
    @2
    @15
    @16
    @50
    @35
    @8
    @14
    @15
    @16
    simp3l
    @8
    @14
    @15
    @16
    simp3r
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
    cA
    cB
    @24
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    @18
    @20
    cA
    wcel
    #
    @44
    @18
    @2
    @19
    cT
    wcel
    #
    @10
    @52
    @35
    @18
    @2
    @4
    @7
    @9
    @12
    @13
    @53
    @35
    @36
    @2
    @4
    @7
    @14
    @17
    simp13
    #
    @38
    @39
    @40
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
    @10
    @11
    @9
    @13
    @8
    @17
    simp22l
    #
    cA
    cP
    cT
    @19
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
    @20
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    #
    cB
    c.or
    cK
    c.le
    @22
    @24
    @20
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    latjlej2
    syl13anc
    mpd
    @18
    @28
    @30
    c.le
    wbr
    #
    @32
    @18
    @2
    @4
    @7
    @9
    @12
    @13
    @59
    @35
    @36
    @54
    @38
    @39
    @40
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
    cdlemk39s
    syl132anc
    @18
    @41
    @28
    cB
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
    @59
    @32
    wi
    @46
    @18
    @2
    @53
    @60
    @35
    @55
    cB
    cR
    cT
    @19
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
    @18
    @30
    cA
    wcel
    #
    @61
    @18
    @2
    @5
    @6
    @64
    @35
    @5
    @6
    @2
    @4
    @14
    @17
    simp13l
    @5
    @6
    @2
    @4
    @14
    @17
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
    cA
    cB
    @30
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    @18
    @27
    cA
    wcel
    #
    @62
    @18
    @2
    @47
    @10
    @66
    @35
    @48
    @56
    cA
    cP
    cT
    @21
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
    @27
    cK
    cdlemk5.b
    cdlemk5.a
    atbase
    syl
    #
    cB
    c.or
    cK
    c.le
    @28
    @30
    @27
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    latjlej2
    syl13anc
    mpd
    @18
    @41
    @23
    cB
    wcel
    #
    @25
    cB
    wcel
    #
    @29
    cB
    wcel
    #
    @31
    cB
    wcel
    #
    @26
    @32
    wa
    @33
    wi
    @46
    @18
    @41
    @44
    @42
    @69
    @46
    @58
    @49
    cB
    c.or
    cK
    @20
    @22
    cdlemk5.b
    cdlemk5.j
    latjcl
    syl3anc
    @18
    @0
    @52
    @50
    @70
    @45
    @57
    @51
    cA
    cB
    c.or
    cK
    @20
    @24
    cdlemk5.b
    cdlemk5.j
    cdlemk5.a
    hlatjcl
    syl3anc
    @18
    @41
    @62
    @60
    @71
    @46
    @68
    @63
    cB
    c.or
    cK
    @27
    @28
    cdlemk5.b
    cdlemk5.j
    latjcl
    syl3anc
    @18
    @0
    @66
    @64
    @72
    @45
    @67
    @65
    cA
    cB
    c.or
    cK
    @27
    @30
    cdlemk5.b
    cdlemk5.j
    cdlemk5.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @31
    @23
    @25
    @29
    cdlemk5.b
    cdlemk5.l
    cdlemk5.m
    latmlem12
    syl122anc
    mp2and
end
