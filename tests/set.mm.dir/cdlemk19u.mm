include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp1.mm"
include "simp2l.mm"
include "simp2r.mm"
include "simp3.mm"
include "cdlemk35u.mm"
include "syl131anc.mm"
include "simpr.mm"
include "simpl2l.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cdlemk40t.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "fveq1.mm"
include "adantl.mm"
include "eqtrd.mm"
include "simpl1.mm"
include "simpl2r.mm"
include "simpl3.mm"
include "cdlemk19u1.mm"
include "pm2.61dane.mm"
include "cdlemd.mm"
include "syl311anc.mm"

theorem cdlemk19u
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cF: class F
  let cH: class H
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
  let cG: class G
  let cI: class I
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
  assume cdlemk5.u: |- U = ( g e. T |-> if ( F = N , g , X ) )

  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
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
  disjoint G g
  disjoint G z
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F e. T /\ N e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( U ` F ) = N )

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
    #
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
    #
    cN
    cT
    wcel
    #
    wa
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
    @0
    cF
    cU
    cfv
    #
    cT
    wcel
    #
    @5
    @7
    cP
    @9
    cfv
    #
    cP
    cN
    cfv
    #
    wceq
    #
    @9
    cN
    wceq
    @0
    @2
    @6
    @7
    simp1l
    @8
    @3
    @4
    @5
    @4
    @7
    @10
    @3
    @6
    @7
    simp1
    @3
    @4
    @5
    @7
    simp2l
    #
    @3
    @4
    @5
    @7
    simp2r
    #
    @14
    @3
    @6
    @7
    simp3
    #
    vz
    cA
    cB
    cP
    cR
    cT
    cU
    vg
    cF
    cF
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
    cdlemk5.u
    cdlemk35u
    syl131anc
    @15
    @16
    @8
    @13
    cF
    cN
    @8
    cF
    cN
    wceq
    #
    wa
    #
    @11
    cP
    cF
    cfv
    #
    @12
    @18
    cP
    @9
    cF
    @18
    @17
    @4
    @9
    cF
    wceq
    @8
    @17
    simpr
    @4
    @5
    @3
    @7
    @17
    simpl2l
    vb
    cv
    #
    cid
    cB
    cres
    wne
    @20
    cR
    cfv
    #
    @1
    wne
    @21
    vg
    cv
    cR
    cfv
    wne
    w3a
    cP
    vz
    cv
    cfv
    cY
    wceq
    wi
    vb
    cT
    wral
    vz
    cT
    cU
    vg
    cF
    cF
    cN
    cX
    cdlemk5.x
    cdlemk5.u
    cdlemk40t
    syl2anc
    fveq1d
    @17
    @19
    @12
    wceq
    @8
    cP
    cF
    cN
    fveq1
    adantl
    eqtrd
    @8
    cF
    cN
    wne
    #
    wa
    @3
    @4
    @22
    @5
    @7
    @13
    @3
    @6
    @7
    @22
    simpl1
    @4
    @5
    @3
    @7
    @22
    simpl2l
    @8
    @22
    simpr
    @4
    @5
    @3
    @7
    @22
    simpl2r
    @3
    @6
    @7
    @22
    simpl3
    vz
    cA
    cB
    cP
    cR
    cT
    cU
    vg
    cF
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
    cdlemk5.u
    cdlemk19u1
    syl131anc
    pm2.61dane
    cA
    cP
    cT
    @9
    cN
    cH
    cK
    c.le
    cW
    cdlemk5.l
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemd
    syl311anc
end
