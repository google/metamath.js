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
include "ccom.mm"
include "wrex.mm"
include "csb.mm"
include "simp1ll.mm"
include "simp1lr.mm"
include "cdlemftr2.mm"
include "syl2anc.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp2.mm"
include "simp3.mm"
include "cdlemk55a.mm"
include "syl113anc.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem cdlemk55b
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ G e. T /\ ( P e. A /\ -. P .<_ W ) ) /\ ( I e. T /\ ( R ` G ) = ( R ` I ) ) ) -> [_ ( G o. I ) / g ]_ X = ( [_ G / g ]_ X o. [_ I / g ]_ X ) )

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
    cF
    cR
    cfv
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
    cF
    cid
    cB
    cres
    #
    wne
    cN
    cT
    wcel
    w3a
    cG
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
    w3a
    #
    cI
    cT
    wcel
    cG
    cR
    cfv
    #
    cI
    cR
    cfv
    wceq
    wa
    #
    w3a
    #
    vj
    cv
    #
    @4
    wne
    @9
    cR
    cfv
    #
    @6
    wne
    @10
    cG
    cI
    ccom
    #
    cR
    cfv
    #
    wne
    w3a
    #
    vj
    cT
    wrex
    #
    vg
    @11
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
    @8
    @0
    @1
    @14
    @0
    @1
    @2
    @5
    @7
    simp1ll
    @0
    @1
    @2
    @5
    @7
    simp1lr
    cB
    cR
    cT
    vj
    cH
    cK
    cW
    @6
    @12
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemftr2
    syl2anc
    @8
    @13
    @15
    vj
    cT
    @8
    @9
    cT
    wcel
    #
    @13
    w3a
    @3
    @5
    @7
    @16
    @13
    @15
    @3
    @5
    @7
    @16
    @13
    simp11
    @3
    @5
    @7
    @16
    @13
    simp12
    @3
    @5
    @7
    @16
    @13
    simp13
    @8
    @16
    @13
    simp2
    @8
    @16
    @13
    simp3
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    vj
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
    cdlemk55a
    syl113anc
    rexlimdv3a
    mpd
end
