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
include "simp3.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simp22l.mm"
include "ltrnat.mm"
include "atbase.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "latlej1.mm"
include "trlcoabs.mm"
include "syl121anc.mm"
include "breqtrd.mm"

theorem cdlemk48
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) ) ) -> ( ( [_ G / g ]_ X o. [_ I / g ]_ X ) ` P ) .<_ ( ( [_ I / g ]_ X ` P ) .\/ ( R ` [_ G / g ]_ X ) ) )

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
    @18
    @15
    cR
    cfv
    #
    c.or
    co
    #
    cP
    @16
    cfv
    @19
    c.or
    co
    #
    c.le
    @14
    cK
    clat
    wcel
    #
    @18
    cB
    wcel
    #
    @19
    cB
    wcel
    #
    @18
    @20
    c.le
    wbr
    @14
    @0
    @22
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
    @14
    @18
    cA
    wcel
    #
    @23
    @14
    @2
    @17
    cT
    wcel
    #
    @8
    @25
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
    @26
    @27
    @14
    @2
    @4
    @5
    @7
    @10
    @11
    @28
    @27
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
    @29
    @27
    @30
    @6
    @12
    @13
    simp3
    @31
    @32
    @33
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
    @2
    @28
    @24
    @27
    @34
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
    c.le
    @18
    @19
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    latlej1
    syl3anc
    @14
    @2
    @28
    @29
    @10
    @20
    @21
    wceq
    @27
    @34
    @35
    @32
    cA
    cP
    cR
    cT
    @15
    @16
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
    trlcoabs
    syl121anc
    breqtrd
end
