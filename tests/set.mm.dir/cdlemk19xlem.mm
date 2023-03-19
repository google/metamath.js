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
include "cv.mm"
include "csb.mm"
include "simp1l.mm"
include "simp2l1.mm"
include "simp2l2.mm"
include "jca.mm"
include "simp2l3.mm"
include "simp2r.mm"
include "simp1r.mm"
include "simp3l.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "3jca.mm"
include "cdlemk42.mm"
include "syl332anc.mm"
include "simp3.mm"
include "cdlemk19y.mm"
include "syl231anc.mm"
include "eqtrd.mm"

theorem cdlemk19xlem
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ ( P e. A /\ -. P .<_ W ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) ) ) ) -> ( [_ F / g ]_ X ` P ) = ( N ` P ) )

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
    cid
    cB
    cres
    #
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
    wa
    #
    vb
    cv
    #
    cT
    wcel
    #
    @11
    @5
    wne
    #
    @11
    cR
    cfv
    @1
    wne
    #
    wa
    #
    wa
    #
    w3a
    #
    cP
    vg
    cF
    cX
    csb
    cfv
    #
    vg
    cF
    cY
    csb
    #
    cP
    cN
    cfv
    #
    @17
    @0
    @4
    @6
    wa
    #
    @21
    @7
    @9
    @2
    @12
    @13
    @14
    @14
    w3a
    @18
    @19
    wceq
    @0
    @2
    @10
    @16
    simp1l
    #
    @17
    @4
    @6
    @4
    @6
    @7
    @9
    @3
    @16
    simp2l1
    @4
    @6
    @7
    @9
    @3
    @16
    simp2l2
    jca
    #
    @23
    @4
    @6
    @7
    @9
    @3
    @16
    simp2l3
    #
    @3
    @8
    @9
    @16
    simp2r
    #
    @0
    @2
    @10
    @16
    simp1r
    #
    @3
    @10
    @12
    @15
    simp3l
    @17
    @13
    @14
    @14
    @13
    @14
    @12
    @3
    @10
    simp3rl
    @13
    @14
    @12
    @3
    @10
    simp3rr
    #
    @27
    3jca
    vz
    cA
    cB
    cP
    cR
    cT
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
    cdlemk42
    syl332anc
    @17
    @0
    @21
    @7
    @9
    @2
    @16
    @19
    @20
    wceq
    @22
    @23
    @24
    @25
    @26
    @3
    @10
    @16
    simp3
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
    cdlemk19y
    syl231anc
    eqtrd
end
