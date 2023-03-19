include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "ccom.mm"
include "csb.mm"
include "cid.mm"
include "cres.mm"
include "simp11.mm"
include "simp21l.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21r.mm"
include "trlnid.mm"
include "syl122anc.mm"
include "3jca.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3.mm"
include "cdlemk55.mm"
include "syl231anc.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cdlemk40f.mm"
include "syl2anc.mm"
include "coeq12d.mm"
include "3eqtr4d.mm"

theorem cdlemk55u1
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ N e. T ) /\ ( ( ( R ` F ) = ( R ` N ) /\ F =/= N ) /\ G e. T /\ I e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( U ` ( G o. I ) ) = ( ( U ` G ) o. ( U ` I ) ) )

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
    cF
    cN
    wne
    #
    wa
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
    #
    cX
    csb
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
    #
    @13
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
    @12
    @0
    @5
    @1
    cF
    cid
    cB
    cres
    #
    wne
    #
    @2
    w3a
    @8
    @9
    @11
    @14
    @17
    wceq
    @0
    @1
    @2
    @10
    @11
    simp11
    #
    @5
    @6
    @8
    @9
    @3
    @11
    simp21l
    #
    @12
    @1
    @22
    @2
    @0
    @1
    @2
    @10
    @11
    simp12
    #
    @12
    @0
    @1
    @2
    @6
    @5
    @22
    @23
    @25
    @0
    @1
    @2
    @10
    @11
    simp13
    #
    @5
    @6
    @8
    @9
    @3
    @11
    simp21r
    #
    @24
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
    @26
    3jca
    @3
    @7
    @8
    @9
    @11
    simp22
    #
    @3
    @7
    @8
    @9
    @11
    simp23
    #
    @3
    @10
    @11
    simp3
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
    cdlemk55
    syl231anc
    @12
    @6
    @13
    cT
    wcel
    #
    @18
    @14
    wceq
    @27
    @12
    @0
    @8
    @9
    @30
    @23
    @28
    @29
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
    vb
    cv
    #
    @21
    wne
    @31
    cR
    cfv
    #
    @4
    wne
    @32
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
    @13
    cN
    cX
    cdlemk5.x
    cdlemk5.u
    cdlemk40f
    syl2anc
    @12
    @19
    @15
    @20
    @16
    @12
    @6
    @8
    @19
    @15
    wceq
    @27
    @28
    @33
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
    @12
    @6
    @9
    @20
    @16
    wceq
    @27
    @29
    @33
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
    cdlemk40f
    syl2anc
    coeq12d
    3eqtr4d
end
