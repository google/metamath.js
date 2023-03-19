include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "ccom.mm"
include "csb.mm"
include "simp11l.mm"
include "simp11r.mm"
include "jca.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp31.mm"
include "ltrnco.mm"
include "syl211anc.mm"
include "simp33.mm"
include "trlconid.mm"
include "syl121anc.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "cdlemk35s.mm"
include "syl132anc.mm"
include "simp13.mm"
include "simp32.mm"
include "cdlemk52.mm"
include "eqcomd.mm"
include "cdlemd.mm"
include "syl311anc.mm"

theorem cdlemk53a
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` I ) ) ) -> [_ ( G o. I ) / g ]_ X = ( [_ G / g ]_ X o. [_ I / g ]_ X ) )

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
    cF
    cid
    cB
    cres
    #
    wne
    wa
    #
    cG
    cT
    wcel
    #
    cG
    @3
    wne
    #
    wa
    #
    w3a
    #
    cN
    cT
    wcel
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
    cF
    cR
    cfv
    cN
    cR
    cfv
    wceq
    #
    w3a
    #
    cI
    cT
    wcel
    #
    cI
    @3
    wne
    #
    cG
    cR
    cfv
    cI
    cR
    cfv
    wne
    #
    w3a
    #
    w3a
    #
    @2
    vg
    cG
    cI
    ccom
    #
    cX
    csb
    #
    cT
    wcel
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
    cT
    wcel
    #
    @10
    cP
    @19
    cfv
    #
    cP
    @23
    cfv
    #
    wceq
    @19
    @23
    wceq
    @17
    @0
    @1
    @0
    @1
    @4
    @7
    @12
    @16
    simp11l
    #
    @0
    @1
    @4
    @7
    @12
    @16
    simp11r
    #
    jca
    #
    @17
    @2
    @4
    @18
    cT
    wcel
    #
    @18
    @3
    wne
    #
    wa
    @9
    @10
    @11
    @20
    @29
    @2
    @4
    @7
    @12
    @16
    simp12
    #
    @17
    @30
    @31
    @17
    @0
    @1
    @5
    @13
    @30
    @27
    @28
    @5
    @6
    @2
    @4
    @12
    @16
    simp13l
    #
    @8
    @12
    @13
    @14
    @15
    simp31
    #
    cT
    cG
    cI
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl211anc
    @17
    @2
    @5
    @13
    @15
    @31
    @29
    @33
    @34
    @8
    @12
    @13
    @14
    @15
    simp33
    cB
    cR
    cT
    cG
    cI
    cH
    cK
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlconid
    syl121anc
    jca
    @8
    @9
    @10
    @11
    @16
    simp21
    #
    @8
    @9
    @10
    @11
    @16
    simp22
    #
    @8
    @9
    @10
    @11
    @16
    simp23
    #
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    @18
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
    cdlemk35s
    syl132anc
    @17
    @0
    @1
    @21
    cT
    wcel
    #
    @22
    cT
    wcel
    #
    @24
    @27
    @28
    @17
    @2
    @4
    @7
    @9
    @10
    @11
    @38
    @29
    @32
    @2
    @4
    @7
    @12
    @16
    simp13
    @35
    @36
    @37
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
    cdlemk35s
    syl132anc
    @17
    @2
    @4
    @13
    @14
    wa
    @9
    @10
    @11
    @39
    @29
    @32
    @17
    @13
    @14
    @34
    @8
    @12
    @13
    @14
    @15
    simp32
    jca
    @35
    @36
    @37
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    cI
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
    cdlemk35s
    syl132anc
    cT
    @21
    @22
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl211anc
    @36
    @17
    @26
    @25
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
    cdlemk52
    eqcomd
    cA
    cP
    cT
    @19
    @23
    cH
    cK
    c.le
    cW
    cdlemk5.l
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemd
    syl311anc
end
