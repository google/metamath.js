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
include "csb.mm"
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "cdlemk11tb.mm"
include "simp31.mm"
include "simp32.mm"
include "jca.mm"
include "cdlemk42.mm"
include "syld3an3.mm"
include "simp11.mm"
include "simp12.mm"
include "simp331.mm"
include "simp332.mm"
include "simp2.mm"
include "simp321.mm"
include "simp322.mm"
include "simp333.mm"
include "3jca.mm"
include "syl312anc.mm"
include "oveq1d.mm"
include "3brtr4d.mm"

theorem cdlemk11tc
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` I ) ) ) ) -> ( [_ G / g ]_ X ` P ) .<_ ( ( [_ I / g ]_ X ` P ) .\/ ( R ` ( I o. `' G ) ) ) )

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
    @1
    wne
    wa
    #
    w3a
    #
    cN
    cT
    wcel
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    w3a
    #
    vb
    cv
    #
    cT
    wcel
    #
    @7
    @1
    wne
    #
    @7
    cR
    cfv
    #
    @5
    wne
    #
    @10
    cG
    cR
    cfv
    wne
    #
    w3a
    #
    cI
    cT
    wcel
    #
    cI
    @1
    wne
    #
    @10
    cI
    cR
    cfv
    wne
    #
    w3a
    #
    w3a
    #
    w3a
    #
    vg
    cG
    cY
    csb
    #
    vg
    cI
    cY
    csb
    #
    cI
    cG
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    cP
    vg
    cG
    cX
    csb
    cfv
    #
    cP
    vg
    cI
    cX
    csb
    cfv
    #
    @22
    c.or
    co
    c.le
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
    cdlemk11tb
    @4
    @6
    @18
    @8
    @13
    wa
    @23
    @20
    wceq
    @19
    @8
    @13
    @4
    @6
    @8
    @13
    @17
    simp31
    #
    @4
    @6
    @8
    @13
    @17
    simp32
    jca
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
    cdlemk42
    syld3an3
    @19
    @24
    @21
    @22
    c.or
    @19
    @0
    @2
    @14
    @15
    wa
    @6
    @8
    @9
    @11
    @16
    w3a
    @24
    @21
    wceq
    @0
    @2
    @3
    @6
    @18
    simp11
    @0
    @2
    @3
    @6
    @18
    simp12
    @19
    @14
    @15
    @14
    @15
    @16
    @8
    @13
    @4
    @6
    simp331
    @14
    @15
    @16
    @8
    @13
    @4
    @6
    simp332
    jca
    @4
    @6
    @18
    simp2
    @25
    @19
    @9
    @11
    @16
    @9
    @11
    @12
    @8
    @17
    @4
    @6
    simp321
    @9
    @11
    @12
    @8
    @17
    @4
    @6
    simp322
    @14
    @15
    @16
    @8
    @13
    @4
    @6
    simp333
    3jca
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
    cdlemk42
    syl312anc
    oveq1d
    3brtr4d
end
