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
include "cv.mm"
include "csb.mm"
include "simp13l.mm"
include "wsbc.mm"
include "wi.mm"
include "cdlemk36.mm"
include "sbcth.mm"
include "sbcimg.mm"
include "mpbid.mm"
include "eleq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "3anbi3d.mm"
include "fveq2.mm"
include "neeq2d.mm"
include "anbi2d.mm"
include "3anbi13d.mm"
include "sbcieg.mm"
include "sbceqg.mm"
include "csbfv12.mm"
include "csbconstg.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "3imtr3d.mm"
include "mpcom.mm"

theorem cdlemk42
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) ) ) -> ( [_ G / g ]_ X ` P ) = [_ G / g ]_ Y )

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
    w3a
    #
    cN
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    w3a
    #
    vb
    cv
    #
    cT
    wcel
    #
    @9
    @2
    wne
    #
    @9
    cR
    cfv
    #
    @7
    wne
    #
    @12
    cG
    cR
    cfv
    #
    wne
    #
    w3a
    #
    wa
    #
    w3a
    #
    cP
    vg
    cG
    cX
    csb
    #
    cfv
    #
    vg
    cG
    cY
    csb
    #
    wceq
    #
    @0
    @4
    @1
    @3
    @8
    @17
    simp13l
    @0
    @1
    @3
    vg
    cv
    #
    cT
    wcel
    #
    @23
    @2
    wne
    #
    wa
    #
    w3a
    #
    @8
    @10
    @11
    @13
    @12
    @23
    cR
    cfv
    #
    wne
    #
    w3a
    #
    wa
    #
    w3a
    #
    vg
    cG
    wsbc
    #
    cP
    cX
    cfv
    #
    cY
    wceq
    #
    vg
    cG
    wsbc
    #
    @18
    @22
    @0
    @32
    @35
    wi
    #
    vg
    cG
    wsbc
    @33
    @36
    wi
    @37
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
    @23
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
    cdlemk36
    sbcth
    @32
    @35
    vg
    cG
    cT
    sbcimg
    mpbid
    @32
    @18
    vg
    cG
    cT
    @23
    cG
    wceq
    #
    @27
    @6
    @31
    @17
    @8
    @38
    @26
    @5
    @1
    @3
    @38
    @24
    @0
    @25
    @4
    @23
    cG
    cT
    eleq1
    @23
    cG
    @2
    neeq1
    anbi12d
    3anbi3d
    @38
    @30
    @16
    @10
    @38
    @29
    @15
    @11
    @13
    @38
    @28
    @14
    @12
    @23
    cG
    cR
    fveq2
    neeq2d
    3anbi3d
    anbi2d
    3anbi13d
    sbcieg
    @0
    @36
    vg
    cG
    @34
    csb
    #
    @21
    wceq
    @22
    vg
    cG
    @34
    cY
    cT
    sbceqg
    @0
    @39
    @20
    @21
    @0
    @39
    vg
    cG
    cP
    csb
    #
    @19
    cfv
    @20
    vg
    cG
    cP
    cX
    csbfv12
    @0
    @40
    cP
    @19
    vg
    cG
    cP
    cT
    csbconstg
    fveq2d
    syl5eq
    eqeq1d
    bitrd
    3imtr3d
    mpcom
end
