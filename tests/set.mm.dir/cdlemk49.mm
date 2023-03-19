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
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "cdlemk35s.mm"
include "syl132anc.mm"
include "simp3.mm"
include "ltrncom.mm"
include "syl3anc.mm"
include "fveq1d.mm"
include "simp2.mm"
include "cdlemk48.mm"
include "syl311anc.mm"
include "eqbrtrd.mm"

theorem cdlemk49
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) ) ) -> ( ( [_ G / g ]_ X o. [_ I / g ]_ X ) ` P ) .<_ ( ( [_ G / g ]_ X ` P ) .\/ ( R ` [_ I / g ]_ X ) ) )

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
    @1
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
    cP
    @12
    @11
    ccom
    #
    cfv
    #
    cP
    @11
    cfv
    @12
    cR
    cfv
    c.or
    co
    #
    c.le
    @10
    cP
    @13
    @14
    @10
    @0
    @11
    cT
    wcel
    #
    @12
    cT
    wcel
    #
    @13
    @14
    wceq
    @0
    @2
    @3
    @8
    @9
    simp11
    #
    @10
    @0
    @2
    @3
    @5
    @6
    @7
    @17
    @19
    @0
    @2
    @3
    @8
    @9
    simp12
    #
    @0
    @2
    @3
    @8
    @9
    simp13
    #
    @4
    @5
    @6
    @7
    @9
    simp21
    #
    @4
    @5
    @6
    @7
    @9
    simp22
    #
    @4
    @5
    @6
    @7
    @9
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
    @10
    @0
    @2
    @9
    @5
    @6
    @7
    @18
    @19
    @20
    @4
    @8
    @9
    simp3
    #
    @22
    @23
    @24
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
    cT
    @11
    @12
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrncom
    syl3anc
    fveq1d
    @10
    @0
    @2
    @9
    @8
    @3
    @15
    @16
    c.le
    wbr
    @19
    @20
    @25
    @4
    @8
    @9
    simp2
    @21
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
    cG
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
    syl311anc
    eqbrtrd
end
