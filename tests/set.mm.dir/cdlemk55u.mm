include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "ccom.mm"
include "simpr.mm"
include "simp11.mm"
include "simp22.mm"
include "simp23.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "adantr.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cdlemk40t.mm"
include "syl2anc.mm"
include "simpl22.mm"
include "simpl23.mm"
include "coeq12d.mm"
include "eqtr4d.mm"
include "simpl1.mm"
include "simpl21.mm"
include "jca.mm"
include "simpl3.mm"
include "cdlemk55u1.mm"
include "syl131anc.mm"
include "pm2.61dane.mm"

theorem cdlemk55u
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
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
  assume cdlemk5.u: |- U = ( g e. T |-> if ( F = N , g , X ) )

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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ N e. T ) /\ ( ( R ` F ) = ( R ` N ) /\ G e. T /\ I e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( U ` ( G o. I ) ) = ( ( U ` G ) o. ( U ` I ) ) )

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
    #
    cN
    cT
    wcel
    #
    w3a
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
    cG
    cI
    ccom
    #
    cU
    cfv
    #
    cG
    cU
    cfv
    #
    cI
    cU
    cfv
    #
    ccom
    #
    wceq
    #
    cF
    cN
    @10
    cF
    cN
    wceq
    #
    wa
    #
    @12
    @11
    @15
    @18
    @17
    @11
    cT
    wcel
    #
    @12
    @11
    wceq
    @10
    @17
    simpr
    #
    @10
    @19
    @17
    @10
    @0
    @6
    @7
    @19
    @0
    @1
    @2
    @8
    @9
    simp11
    @3
    @5
    @6
    @7
    @9
    simp22
    @3
    @5
    @6
    @7
    @9
    simp23
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
    adantr
    vb
    cv
    #
    cid
    cB
    cres
    wne
    @21
    cR
    cfv
    #
    @4
    wne
    @22
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
    #
    vz
    cT
    cU
    vg
    cF
    @11
    cN
    cX
    cdlemk5.x
    cdlemk5.u
    cdlemk40t
    syl2anc
    @18
    @13
    cG
    @14
    cI
    @18
    @17
    @6
    @13
    cG
    wceq
    @20
    @5
    @6
    @7
    @3
    @9
    @17
    simpl22
    @23
    vz
    cT
    cU
    vg
    cF
    cG
    cN
    cX
    cdlemk5.x
    cdlemk5.u
    cdlemk40t
    syl2anc
    @18
    @17
    @7
    @14
    cI
    wceq
    @20
    @5
    @6
    @7
    @3
    @9
    @17
    simpl23
    @23
    vz
    cT
    cU
    vg
    cF
    cI
    cN
    cX
    cdlemk5.x
    cdlemk5.u
    cdlemk40t
    syl2anc
    coeq12d
    eqtr4d
    @10
    cF
    cN
    wne
    #
    wa
    #
    @3
    @5
    @24
    wa
    @6
    @7
    @9
    @16
    @3
    @8
    @9
    @24
    simpl1
    @25
    @5
    @24
    @5
    @6
    @7
    @3
    @9
    @24
    simpl21
    @10
    @24
    simpr
    jca
    @5
    @6
    @7
    @3
    @9
    @24
    simpl22
    @5
    @6
    @7
    @3
    @9
    @24
    simpl23
    @3
    @8
    @9
    @24
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
    cdlemk5.u
    cdlemk55u1
    syl131anc
    pm2.61dane
end
