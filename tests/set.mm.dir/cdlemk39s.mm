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
include "cdlemk39.mm"
include "sbcth.mm"
include "sbcimg.mm"
include "mpbid.mm"
include "eleq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "3anbi2d.mm"
include "sbcieg.mm"
include "sbcbr12g.mm"
include "csbfv2g.mm"
include "csbfv.mm"
include "a1i.mm"
include "breq12d.mm"
include "bitrd.mm"
include "3imtr3d.mm"
include "mpcom.mm"

theorem cdlemk39s
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> ( R ` [_ G / g ]_ X ) .<_ ( R ` G ) )

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
    @13
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
    cR
    cfv
    #
    @13
    cR
    cfv
    #
    c.le
    wbr
    #
    vg
    cG
    wsbc
    #
    @9
    @12
    @0
    @18
    @22
    wi
    #
    vg
    cG
    wsbc
    @19
    @23
    wi
    @24
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
    @13
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
    cdlemk39
    sbcth
    @18
    @22
    vg
    cG
    cT
    sbcimg
    mpbid
    @18
    @9
    vg
    cG
    cT
    @13
    cG
    wceq
    #
    @17
    @7
    @1
    @8
    @25
    @16
    @5
    @3
    @6
    @25
    @14
    @0
    @15
    @4
    @13
    cG
    cT
    eleq1
    @13
    cG
    @2
    neeq1
    anbi12d
    3anbi2d
    3anbi2d
    sbcieg
    @0
    @23
    vg
    cG
    @20
    csb
    #
    vg
    cG
    @21
    csb
    #
    c.le
    wbr
    @12
    vg
    cG
    @20
    @21
    c.le
    cT
    sbcbr12g
    @0
    @26
    @10
    @27
    @11
    c.le
    vg
    cG
    cX
    cT
    cR
    csbfv2g
    @27
    @11
    wceq
    @0
    vg
    cG
    cR
    csbfv
    a1i
    breq12d
    bitrd
    3imtr3d
    mpcom
end
