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
include "ccom.mm"
include "csb.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl3.mm"
include "simpl23.mm"
include "simpr.mm"
include "cdlemk55b.mm"
include "syl132anc.mm"
include "cdlemk53.mm"
include "pm2.61dane.mm"

theorem cdlemk55
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
  let vj: setvar j
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
  disjoint .<_ j
  disjoint A j
  disjoint B j
  disjoint F j
  disjoint G j
  disjoint H j
  disjoint I j
  disjoint K j
  disjoint N j
  disjoint P j
  disjoint R j
  disjoint T j
  disjoint W j
  disjoint X j
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ G e. T /\ I e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> [_ ( G o. I ) / g ]_ X = ( [_ G / g ]_ X o. [_ I / g ]_ X ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
    cR
    cfv
    cN
    cR
    cfv
    wceq
    wa
    #
    cF
    cT
    wcel
    cF
    cid
    cB
    cres
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
    cI
    cT
    wcel
    #
    w3a
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
    vg
    cG
    cI
    ccom
    cX
    csb
    vg
    cG
    cX
    csb
    vg
    cI
    cX
    csb
    ccom
    wceq
    #
    cG
    cR
    cfv
    #
    cI
    cR
    cfv
    #
    @6
    @8
    @9
    wceq
    #
    wa
    @0
    @1
    @2
    @5
    @3
    @10
    @7
    @0
    @4
    @5
    @10
    simpl1
    @1
    @2
    @3
    @0
    @5
    @10
    simpl21
    @1
    @2
    @3
    @0
    @5
    @10
    simpl22
    @0
    @4
    @5
    @10
    simpl3
    @1
    @2
    @3
    @0
    @5
    @10
    simpl23
    @6
    @10
    simpr
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
    cdlemk55b
    syl132anc
    @6
    @8
    @9
    wne
    #
    wa
    @0
    @1
    @2
    @5
    @3
    @11
    @7
    @0
    @4
    @5
    @11
    simpl1
    @1
    @2
    @3
    @0
    @5
    @11
    simpl21
    @1
    @2
    @3
    @0
    @5
    @11
    simpl22
    @0
    @4
    @5
    @11
    simpl3
    @1
    @2
    @3
    @0
    @5
    @11
    simpl23
    @6
    @11
    simpr
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
    cdlemk53
    syl132anc
    pm2.61dane
end
