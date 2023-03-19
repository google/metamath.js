include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wn.mm"
include "simp11.mm"
include "wfn.mm"
include "cv.mm"
include "wral.mm"
include "wf.mm"
include "cif.mm"
include "cvv.mm"
include "vex.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wi.mm"
include "crio.mm"
include "riotaex.mm"
include "eqeltri.mm"
include "ifex.mm"
include "rgenw.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "simpl11.mm"
include "simpl2.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpr.mm"
include "simpl3.mm"
include "cdlemk35u.mm"
include "syl231anc.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "ccom.mm"
include "simp12.mm"
include "simp2.mm"
include "simp3.mm"
include "simp13.mm"
include "cdlemk55u.mm"
include "syl131anc.mm"
include "simpl1.mm"
include "cdlemk39u.mm"
include "syl121anc.mm"
include "istendod.mm"

theorem cdlemk56
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let cE: class E
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
  let vf: setvar f
  let vh: setvar h
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
  assume cdlemk5.e: |- E = ( ( TEndo ` K ) ` W )

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
  disjoint f h
  disjoint .<_ f
  disjoint .<_ h
  disjoint A f
  disjoint A h
  disjoint F f
  disjoint F h
  disjoint H f
  disjoint H h
  disjoint K f
  disjoint K h
  disjoint N f
  disjoint N h
  disjoint P f
  disjoint P h
  disjoint R f
  disjoint R h
  disjoint T f
  disjoint T h
  disjoint U f
  disjoint U h
  disjoint W f
  disjoint W h
  disjoint b f
  disjoint b h
  disjoint f g
  disjoint f z
  disjoint g h
  disjoint h z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ N e. T ) /\ ( R ` F ) = ( R ` N ) /\ ( P e. A /\ -. P .<_ W ) ) -> U e. E )

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
    cR
    cU
    cT
    vf
    vh
    cE
    cH
    cK
    c.le
    chlt
    cW
    cdlemk5.l
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5.e
    @0
    @1
    @2
    @5
    @6
    simp11
    @7
    cU
    cT
    wfn
    #
    vf
    cv
    #
    cU
    cfv
    #
    cT
    wcel
    #
    vf
    cT
    wral
    cT
    cT
    cU
    wf
    cF
    cN
    wceq
    #
    vg
    cv
    #
    cX
    cif
    #
    cvv
    wcel
    #
    vg
    cT
    wral
    @8
    @7
    @15
    vg
    cT
    @12
    @13
    cX
    vg
    vex
    cX
    vb
    cv
    #
    cid
    cB
    cres
    wne
    @16
    cR
    cfv
    #
    @4
    wne
    @17
    @13
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
    crio
    cvv
    cdlemk5.x
    @18
    vz
    cT
    riotaex
    eqeltri
    ifex
    rgenw
    vg
    cT
    @14
    cU
    cvv
    cdlemk5.u
    fnmpt
    mp1i
    @7
    @11
    vf
    cT
    @7
    @9
    cT
    wcel
    #
    wa
    #
    @0
    @5
    @1
    @2
    @19
    @6
    @11
    @0
    @1
    @2
    @5
    @6
    @19
    simpl11
    @3
    @5
    @6
    @19
    simpl2
    #
    @0
    @1
    @2
    @5
    @6
    @19
    simpl12
    @0
    @1
    @2
    @5
    @6
    @19
    simpl13
    @7
    @19
    simpr
    #
    @3
    @5
    @6
    @19
    simpl3
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
    @9
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
    syl231anc
    ralrimiva
    vf
    cT
    cT
    cU
    ffnfv
    sylanbrc
    @7
    @19
    vh
    cv
    #
    cT
    wcel
    #
    w3a
    @3
    @5
    @19
    @25
    @6
    @9
    @24
    ccom
    cU
    cfv
    @10
    @24
    cU
    cfv
    ccom
    wceq
    @3
    @5
    @6
    @19
    @25
    simp11
    @3
    @5
    @6
    @19
    @25
    simp12
    @7
    @19
    @25
    simp2
    @7
    @19
    @25
    simp3
    @3
    @5
    @6
    @19
    @25
    simp13
    vz
    cA
    cB
    cP
    cR
    cT
    cU
    vg
    cF
    @9
    cH
    @24
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
    cdlemk55u
    syl131anc
    @20
    @3
    @5
    @19
    @6
    @10
    cR
    cfv
    @9
    cR
    cfv
    c.le
    wbr
    @3
    @5
    @6
    @19
    simpl1
    @21
    @22
    @23
    vz
    cA
    cB
    cP
    cR
    cT
    cU
    vg
    cF
    @9
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
    cdlemk39u
    syl121anc
    istendod
end
