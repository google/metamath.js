include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "simpr.mm"
include "simpl23.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cdlemk40t.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "csb.mm"
include "cdlemk40f.mm"
include "simpl1l.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl1r.mm"
include "trlnid.mm"
include "syl122anc.mm"
include "jca.mm"
include "simpl3.mm"
include "cdlemk35s-id.mm"
include "syl132anc.mm"
include "pm2.61dane.mm"

theorem cdlemk35u
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F e. T /\ N e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( U ` G ) e. T )

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
    cG
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
    cU
    cfv
    #
    cT
    wcel
    cF
    cN
    @9
    cF
    cN
    wceq
    #
    wa
    #
    @10
    cG
    cT
    @12
    @11
    @6
    @10
    cG
    wceq
    @9
    @11
    simpr
    @4
    @5
    @6
    @3
    @8
    @11
    simpl23
    #
    vb
    cv
    #
    cid
    cB
    cres
    #
    wne
    @14
    cR
    cfv
    #
    @1
    wne
    @16
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
    cG
    cN
    cX
    cdlemk5.x
    cdlemk5.u
    cdlemk40t
    syl2anc
    @13
    eqeltrd
    @9
    cF
    cN
    wne
    #
    wa
    #
    @10
    vg
    cG
    cX
    csb
    #
    cT
    @19
    @18
    @6
    @10
    @20
    wceq
    @9
    @18
    simpr
    #
    @4
    @5
    @6
    @3
    @8
    @18
    simpl23
    #
    @17
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
    cdlemk40f
    syl2anc
    @19
    @0
    @4
    cF
    @15
    wne
    #
    wa
    @6
    @5
    @8
    @2
    @20
    cT
    wcel
    @0
    @2
    @7
    @8
    @18
    simpl1l
    #
    @19
    @4
    @23
    @4
    @5
    @6
    @3
    @8
    @18
    simpl21
    #
    @19
    @0
    @4
    @5
    @18
    @2
    @23
    @24
    @25
    @4
    @5
    @6
    @3
    @8
    @18
    simpl22
    #
    @21
    @0
    @2
    @7
    @8
    @18
    simpl1r
    #
    cB
    cR
    cT
    cF
    cN
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlnid
    syl122anc
    jca
    @22
    @26
    @3
    @7
    @8
    @18
    simpl3
    @27
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
    cdlemk35s-id
    syl132anc
    eqeltrd
    pm2.61dane
end
