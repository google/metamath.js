include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "ccom.mm"
include "csb.mm"
include "coass.mm"
include "csbeq1.mm"
include "ax-mp.mm"
include "simp1.mm"
include "simp21.mm"
include "simp1l.mm"
include "simp22.mm"
include "simp31l.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simp23.mm"
include "simp32.mm"
include "simp333.mm"
include "necomd.mm"
include "cdlemk53.mm"
include "syl132anc.mm"
include "simp2.mm"
include "simp31r.mm"
include "simp332.mm"
include "neeqtrd.mm"
include "simp331.mm"
include "trlcone.mm"
include "syl122anc.mm"
include "eqnetrd.mm"
include "syl112anc.mm"
include "coeq2d.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "3eqtr3a.mm"

theorem cdlemk54
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let vj: setvar j
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
  disjoint b j
  disjoint g j
  disjoint j z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ G e. T /\ ( P e. A /\ -. P .<_ W ) ) /\ ( ( I e. T /\ ( R ` G ) = ( R ` I ) ) /\ j e. T /\ ( j =/= ( _I |` B ) /\ ( R ` j ) =/= ( R ` G ) /\ ( R ` j ) =/= ( R ` ( G o. I ) ) ) ) ) -> ( [_ ( G o. I ) / g ]_ X o. [_ j / g ]_ X ) = ( ( [_ G / g ]_ X o. [_ I / g ]_ X ) o. [_ j / g ]_ X ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cF
    cT
    wcel
    cF
    cid
    cB
    cres
    #
    wne
    cN
    cT
    wcel
    w3a
    #
    cG
    cT
    wcel
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cI
    cT
    wcel
    #
    cG
    cR
    cfv
    #
    cI
    cR
    cfv
    #
    wceq
    #
    wa
    #
    vj
    cv
    #
    cT
    wcel
    #
    @13
    @3
    wne
    #
    @13
    cR
    cfv
    #
    @9
    wne
    #
    @16
    cG
    cI
    ccom
    #
    cR
    cfv
    #
    wne
    #
    w3a
    #
    w3a
    #
    w3a
    #
    vg
    @18
    @13
    ccom
    #
    cX
    csb
    #
    vg
    cG
    cI
    @13
    ccom
    #
    ccom
    #
    cX
    csb
    #
    vg
    @18
    cX
    csb
    vg
    @13
    cX
    csb
    #
    ccom
    #
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
    @29
    ccom
    #
    @24
    @27
    wceq
    @25
    @28
    wceq
    cG
    cI
    @13
    coass
    vg
    @24
    @27
    cX
    csbeq1
    ax-mp
    @23
    @2
    @4
    @18
    cT
    wcel
    #
    @6
    @14
    @19
    @16
    wne
    @25
    @30
    wceq
    @2
    @7
    @22
    simp1
    #
    @2
    @4
    @5
    @6
    @22
    simp21
    #
    @23
    @0
    @5
    @8
    @34
    @0
    @1
    @7
    @22
    simp1l
    #
    @2
    @4
    @5
    @6
    @22
    simp22
    @8
    @11
    @14
    @21
    @2
    @7
    simp31l
    #
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
    @2
    @4
    @5
    @6
    @22
    simp23
    #
    @2
    @7
    @12
    @14
    @21
    simp32
    #
    @23
    @16
    @19
    @15
    @17
    @20
    @12
    @14
    @2
    @7
    simp333
    necomd
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    @18
    cH
    @13
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
    cdlemk53
    syl132anc
    @23
    @28
    @31
    vg
    @26
    cX
    csb
    #
    ccom
    #
    @33
    @23
    @2
    @7
    @26
    cT
    wcel
    #
    @9
    @26
    cR
    cfv
    #
    wne
    @28
    @42
    wceq
    @35
    @2
    @7
    @22
    simp2
    @23
    @0
    @8
    @14
    @43
    @37
    @38
    @40
    cT
    cI
    @13
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl3anc
    @23
    @9
    @10
    @44
    @8
    @11
    @14
    @21
    @2
    @7
    simp31r
    #
    @23
    @0
    @8
    @14
    @10
    @16
    wne
    #
    @15
    @10
    @44
    wne
    @37
    @38
    @40
    @23
    @16
    @10
    @23
    @16
    @9
    @10
    @15
    @17
    @20
    @12
    @14
    @2
    @7
    simp332
    @45
    neeqtrd
    necomd
    #
    @15
    @17
    @20
    @12
    @14
    @2
    @7
    simp331
    cB
    cR
    cT
    cI
    @13
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcone
    syl122anc
    eqnetrd
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
    @26
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
    cdlemk53
    syl112anc
    @23
    @42
    @31
    @32
    @29
    ccom
    #
    ccom
    @33
    @23
    @41
    @48
    @31
    @23
    @2
    @4
    @8
    @6
    @14
    @46
    @41
    @48
    wceq
    @35
    @36
    @38
    @39
    @40
    @47
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
    @13
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
    cdlemk53
    syl132anc
    coeq2d
    @31
    @32
    @29
    coass
    syl6eqr
    eqtrd
    3eqtr3a
end
