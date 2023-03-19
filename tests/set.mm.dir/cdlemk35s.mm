include "wcel.mm"
include "chlt.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "csb.mm"
include "simp22l.mm"
include "cv.mm"
include "wsbc.mm"
include "wi.mm"
include "cdlemk35.mm"
include "sbcth.mm"
include "sbcimg.mm"
include "mpbid.mm"
include "eleq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "3anbi2d.mm"
include "sbcieg.mm"
include "sbcel1g.mm"
include "3imtr3d.mm"
include "mpcom.mm"

theorem cdlemk35s
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> [_ G / g ]_ X e. T )

  proof
    cG
    cT
    wcel
    #
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
    cF
    cid
    cB
    cres
    #
    wne
    wa
    #
    @0
    cG
    @2
    wne
    #
    wa
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
    cF
    cR
    cfv
    cN
    cR
    cfv
    wceq
    wa
    #
    w3a
    #
    vg
    cG
    cX
    csb
    cT
    wcel
    #
    @0
    @4
    @3
    @6
    @1
    @8
    simp22l
    @0
    @1
    @3
    vg
    cv
    #
    cT
    wcel
    #
    @11
    @2
    wne
    #
    wa
    #
    @6
    w3a
    #
    @8
    w3a
    #
    vg
    cG
    wsbc
    #
    cX
    cT
    wcel
    #
    vg
    cG
    wsbc
    #
    @9
    @10
    @0
    @16
    @18
    wi
    #
    vg
    cG
    wsbc
    @17
    @19
    wi
    @20
    vg
    cG
    cT
    vz
    cA
    cB
    cP
    cR
    cT
    cF
    @11
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
    cdlemk35
    sbcth
    @16
    @18
    vg
    cG
    cT
    sbcimg
    mpbid
    @16
    @9
    vg
    cG
    cT
    @11
    cG
    wceq
    #
    @15
    @7
    @1
    @8
    @21
    @14
    @5
    @3
    @6
    @21
    @12
    @0
    @13
    @4
    @11
    cG
    cT
    eleq1
    @11
    cG
    @2
    neeq1
    anbi12d
    3anbi2d
    3anbi2d
    sbcieg
    vg
    cG
    cX
    cT
    cT
    sbcel1g
    3imtr3d
    mpcom
end
