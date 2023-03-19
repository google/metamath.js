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
include "ccom.mm"
include "csb.mm"
include "wf1o.mm"
include "wf.mm"
include "simp1l.mm"
include "simp211.mm"
include "simp212.mm"
include "jca.mm"
include "simp31.mm"
include "simp213.mm"
include "simp23.mm"
include "simp1r.mm"
include "cdlemk35s-id.mm"
include "syl132anc.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "adantr.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "simpl1l.mm"
include "3jca.mm"
include "simpl23.mm"
include "simpr.mm"
include "cdlemkid.mm"
include "syl112anc.mm"
include "coeq1d.mm"
include "simpl31.mm"
include "eqtrd.mm"
include "csbeq1d.mm"
include "3eqtr4rd.mm"
include "simpl22.mm"
include "simpl1r.mm"
include "simpl3.mm"
include "cdlemk53a.mm"
include "syl331anc.mm"
include "pm2.61dane.mm"

theorem cdlemk53b
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ G e. T /\ ( P e. A /\ -. P .<_ W ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` I ) ) ) -> [_ ( G o. I ) / g ]_ X = ( [_ G / g ]_ X o. [_ I / g ]_ X ) )

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
    cG
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
    w3a
    #
    cI
    cT
    wcel
    #
    cI
    @4
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
    wceq
    #
    cG
    @4
    @15
    cG
    @4
    wceq
    #
    wa
    #
    @4
    @19
    ccom
    #
    @19
    @20
    @17
    @23
    cB
    cB
    @19
    wf1o
    #
    cB
    cB
    @19
    wf
    @24
    @19
    wceq
    @15
    @25
    @22
    @15
    @0
    @19
    cT
    wcel
    #
    @25
    @0
    @1
    @10
    @14
    simp1l
    #
    @15
    @0
    @3
    @5
    wa
    #
    @11
    @6
    @9
    @1
    @26
    @27
    @15
    @3
    @5
    @3
    @5
    @6
    @8
    @9
    @2
    @14
    simp211
    #
    @3
    @5
    @6
    @8
    @9
    @2
    @14
    simp212
    jca
    #
    @2
    @10
    @11
    @12
    @13
    simp31
    @3
    @5
    @6
    @8
    @9
    @2
    @14
    simp213
    #
    @2
    @7
    @8
    @9
    @14
    simp23
    @0
    @1
    @10
    @14
    simp1r
    #
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
    cdlemk35s-id
    syl132anc
    cB
    cT
    @19
    cH
    cK
    chlt
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    ltrn1o
    syl2anc
    adantr
    cB
    cB
    @19
    f1of
    cB
    cB
    @19
    fcoi2
    3syl
    @23
    @18
    @4
    @19
    @23
    @0
    @3
    @6
    @1
    w3a
    #
    @9
    @22
    @18
    @4
    wceq
    @0
    @1
    @10
    @14
    @22
    simpl1l
    #
    @15
    @33
    @22
    @15
    @3
    @6
    @1
    @29
    @31
    @32
    3jca
    adantr
    @7
    @8
    @9
    @2
    @14
    @22
    simpl23
    @15
    @22
    simpr
    #
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
    cdlemkid
    syl112anc
    coeq1d
    @23
    vg
    @16
    cI
    cX
    @23
    @16
    @4
    cI
    ccom
    #
    cI
    @23
    cG
    @4
    cI
    @35
    coeq1d
    @23
    cB
    cB
    cI
    wf1o
    #
    cB
    cB
    cI
    wf
    @36
    cI
    wceq
    @23
    @0
    @11
    @37
    @34
    @11
    @12
    @13
    @2
    @10
    @22
    simpl31
    cB
    cT
    cI
    cH
    cK
    chlt
    cW
    cdlemk5.b
    cdlemk5.h
    cdlemk5.t
    ltrn1o
    syl2anc
    cB
    cB
    cI
    f1of
    cB
    cB
    cI
    fcoi2
    3syl
    eqtrd
    csbeq1d
    3eqtr4rd
    @15
    cG
    @4
    wne
    #
    wa
    #
    @0
    @28
    @8
    @38
    wa
    @6
    @9
    @1
    @14
    @21
    @0
    @1
    @10
    @14
    @38
    simpl1l
    @15
    @28
    @38
    @30
    adantr
    @39
    @8
    @38
    @7
    @8
    @9
    @2
    @14
    @38
    simpl22
    @15
    @38
    simpr
    jca
    @15
    @6
    @38
    @31
    adantr
    @7
    @8
    @9
    @2
    @14
    @38
    simpl23
    @0
    @1
    @10
    @14
    @38
    simpl1r
    @2
    @10
    @14
    @38
    simpl3
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
    cdlemk53a
    syl331anc
    pm2.61dane
end
