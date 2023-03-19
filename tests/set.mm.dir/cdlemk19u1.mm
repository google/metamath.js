include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "csb.mm"
include "simp22.mm"
include "simp21.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wi.mm"
include "wral.mm"
include "cdlemk40f.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "simp1l.mm"
include "simp23.mm"
include "simp1r.mm"
include "trlnid.mm"
include "syl122anc.mm"
include "3jca.mm"
include "cdlemk19x.mm"
include "syld3an2.mm"
include "eqtrd.mm"

theorem cdlemk19u1
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F e. T /\ F =/= N /\ N e. T ) /\ ( P e. A /\ -. P .<_ W ) ) -> ( ( U ` F ) ` P ) = ( N ` P ) )

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
    cF
    cN
    wne
    #
    cN
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
    cP
    cF
    cU
    cfv
    #
    cfv
    cP
    vg
    cF
    cX
    csb
    #
    cfv
    #
    cP
    cN
    cfv
    #
    @9
    cP
    @10
    @11
    @9
    @5
    @4
    @10
    @11
    wceq
    @3
    @4
    @5
    @6
    @8
    simp22
    #
    @3
    @4
    @5
    @6
    @8
    simp21
    #
    vb
    cv
    #
    cid
    cB
    cres
    #
    wne
    @16
    cR
    cfv
    #
    @1
    wne
    @18
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
    cdlemk40f
    syl2anc
    fveq1d
    @3
    @4
    cF
    @17
    wne
    #
    @6
    w3a
    @7
    @8
    @12
    @13
    wceq
    @9
    @4
    @19
    @6
    @15
    @9
    @0
    @4
    @6
    @5
    @2
    @19
    @0
    @2
    @7
    @8
    simp1l
    @15
    @3
    @4
    @5
    @6
    @8
    simp23
    #
    @14
    @0
    @2
    @7
    @8
    simp1r
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
    @20
    3jca
    vz
    cA
    cB
    cP
    cR
    cT
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
    cdlemk19x
    syld3an2
    eqtrd
end
