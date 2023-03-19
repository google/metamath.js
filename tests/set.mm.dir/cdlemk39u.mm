include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "simpr.mm"
include "simpl2r.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cdlemk40t.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp11.mm"
include "simp2r.mm"
include "trlcl.mm"
include "latref.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl3.mm"
include "cdlemk39u1.mm"
include "syl131anc.mm"
include "pm2.61dane.mm"

theorem cdlemk39u
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ N e. T ) /\ ( ( R ` F ) = ( R ` N ) /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( R ` ( U ` G ) ) .<_ ( R ` G ) )

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
    cG
    cU
    cfv
    #
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    c.le
    wbr
    #
    cF
    cN
    @11
    cF
    cN
    wceq
    #
    wa
    #
    @13
    @14
    @14
    c.le
    @17
    @12
    cG
    cR
    @17
    @16
    @8
    @12
    cG
    wceq
    @11
    @16
    simpr
    @7
    @8
    @5
    @10
    @16
    simpl2r
    vb
    cv
    #
    cid
    cB
    cres
    wne
    @18
    cR
    cfv
    #
    @6
    wne
    @19
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
    cG
    cN
    cX
    cdlemk5.x
    cdlemk5.u
    cdlemk40t
    syl2anc
    fveq2d
    @11
    @14
    @14
    c.le
    wbr
    #
    @16
    @11
    cK
    clat
    wcel
    #
    @14
    cB
    wcel
    #
    @20
    @11
    @0
    @21
    @0
    @1
    @3
    @4
    @9
    @10
    simp11l
    cK
    hllat
    syl
    @11
    @2
    @8
    @22
    @2
    @3
    @4
    @9
    @10
    simp11
    @5
    @7
    @8
    @10
    simp2r
    cB
    cR
    cT
    cG
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
    cK
    c.le
    @14
    cdlemk5.b
    cdlemk5.l
    latref
    syl2anc
    adantr
    eqbrtrd
    @11
    cF
    cN
    wne
    #
    wa
    @5
    @7
    @23
    @8
    @10
    @15
    @5
    @9
    @10
    @23
    simpl1
    @7
    @8
    @5
    @10
    @23
    simpl2l
    @11
    @23
    simpr
    @7
    @8
    @5
    @10
    @23
    simpl2r
    @5
    @9
    @10
    @23
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
    cdlemk39u1
    syl131anc
    pm2.61dane
end
