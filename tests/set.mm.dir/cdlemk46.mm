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
include "ccom.mm"
include "csb.mm"
include "co.mm"
include "simp11.mm"
include "simp31.mm"
include "simp13l.mm"
include "ltrncom.mm"
include "syl3anc.mm"
include "csbeq1d.mm"
include "fveq1d.mm"
include "simp12.mm"
include "simp32.mm"
include "jca.mm"
include "simp2.mm"
include "simp13r.mm"
include "simp33.mm"
include "eqnetrd.mm"
include "cdlemk45.mm"
include "syl313anc.mm"
include "eqbrtrrd.mm"

theorem cdlemk46
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( G o. I ) =/= ( _I |` B ) ) ) -> ( [_ ( G o. I ) / g ]_ X ` P ) .<_ ( ( [_ G / g ]_ X ` P ) .\/ ( R ` I ) ) )

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
    #
    cG
    @1
    wne
    #
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
    cN
    cR
    cfv
    wceq
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
    cG
    cI
    ccom
    #
    @1
    wne
    #
    w3a
    #
    w3a
    #
    cP
    vg
    cI
    cG
    ccom
    #
    cX
    csb
    #
    cfv
    #
    cP
    vg
    @10
    cX
    csb
    #
    cfv
    cP
    vg
    cG
    cX
    csb
    cfv
    cI
    cR
    cfv
    c.or
    co
    #
    c.le
    @13
    cP
    @15
    @17
    @13
    vg
    @14
    @10
    cX
    @13
    @0
    @8
    @3
    @14
    @10
    wceq
    @0
    @2
    @5
    @7
    @12
    simp11
    #
    @6
    @7
    @8
    @9
    @11
    simp31
    #
    @3
    @4
    @0
    @2
    @7
    @12
    simp13l
    #
    cT
    cI
    cG
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrncom
    syl3anc
    #
    csbeq1d
    fveq1d
    @13
    @0
    @2
    @8
    @9
    wa
    @7
    @3
    @4
    @14
    @1
    wne
    @16
    @18
    c.le
    wbr
    @19
    @0
    @2
    @5
    @7
    @12
    simp12
    @13
    @8
    @9
    @20
    @6
    @7
    @8
    @9
    @11
    simp32
    jca
    @6
    @7
    @12
    simp2
    @21
    @3
    @4
    @0
    @2
    @7
    @12
    simp13r
    @13
    @14
    @10
    @1
    @22
    @6
    @7
    @8
    @9
    @11
    simp33
    eqnetrd
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
    cdlemk45
    syl313anc
    eqbrtrrd
end
