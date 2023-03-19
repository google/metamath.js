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
include "csb.mm"
include "ccnv.mm"
include "wf1o.mm"
include "simp1l.mm"
include "simp211.mm"
include "simp212.mm"
include "jca.mm"
include "simp32.mm"
include "simp213.mm"
include "simp23.mm"
include "simp1r.mm"
include "cdlemk35s-id.mm"
include "syl131anc.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv2.mm"
include "syl.mm"
include "coeq2d.mm"
include "wf.mm"
include "simp22.mm"
include "simp31l.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtr2d.mm"
include "coass.mm"
include "syl6eqr.mm"
include "cdlemk54.mm"
include "coeq1d.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem cdlemk55a
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
  let vg: setvar g
  let vj: setvar j
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
  disjoint b j
  disjoint g j
  disjoint j z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ G e. T /\ ( P e. A /\ -. P .<_ W ) ) /\ ( ( I e. T /\ ( R ` G ) = ( R ` I ) ) /\ j e. T /\ ( j =/= ( _I |` B ) /\ ( R ` j ) =/= ( R ` G ) /\ ( R ` j ) =/= ( R ` ( G o. I ) ) ) ) ) -> [_ ( G o. I ) / g ]_ X = ( [_ G / g ]_ X o. [_ I / g ]_ X ) )

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
    cG
    cR
    cfv
    #
    cI
    cR
    cfv
    wceq
    #
    wa
    #
    vj
    cv
    #
    cT
    wcel
    #
    @15
    @4
    wne
    @15
    cR
    cfv
    #
    @12
    wne
    @17
    cG
    cI
    ccom
    #
    cR
    cfv
    wne
    w3a
    #
    w3a
    #
    w3a
    #
    vg
    @18
    cX
    csb
    #
    @22
    vg
    @15
    cX
    csb
    #
    ccom
    #
    @23
    ccnv
    #
    ccom
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
    @21
    @22
    @22
    @23
    @25
    ccom
    #
    ccom
    #
    @26
    @21
    @31
    @22
    @4
    ccom
    #
    @22
    @21
    @30
    @4
    @22
    @21
    cB
    cB
    @23
    wf1o
    #
    @30
    @4
    wceq
    @21
    @0
    @23
    cT
    wcel
    #
    @33
    @0
    @1
    @10
    @20
    simp1l
    #
    @21
    @0
    @3
    @5
    wa
    #
    @16
    @6
    @9
    @1
    wa
    #
    @34
    @35
    @21
    @3
    @5
    @3
    @5
    @6
    @8
    @9
    @2
    @20
    simp211
    @3
    @5
    @6
    @8
    @9
    @2
    @20
    simp212
    jca
    #
    @2
    @10
    @14
    @16
    @19
    simp32
    @3
    @5
    @6
    @8
    @9
    @2
    @20
    simp213
    #
    @21
    @9
    @1
    @2
    @7
    @8
    @9
    @20
    simp23
    @0
    @1
    @10
    @20
    simp1r
    jca
    #
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    @15
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
    syl131anc
    cB
    cT
    @23
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
    @23
    f1ococnv2
    syl
    #
    coeq2d
    @21
    cB
    cB
    @22
    wf1o
    #
    cB
    cB
    @22
    wf
    @32
    @22
    wceq
    @21
    @0
    @22
    cT
    wcel
    #
    @42
    @35
    @21
    @0
    @36
    @18
    cT
    wcel
    #
    @6
    @37
    @43
    @35
    @38
    @21
    @0
    @8
    @11
    @44
    @35
    @2
    @7
    @8
    @9
    @20
    simp22
    #
    @11
    @13
    @16
    @19
    @2
    @10
    simp31l
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
    syl3anc
    @39
    @40
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
    cdlemk35s-id
    syl131anc
    cB
    cT
    @22
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
    @22
    f1of
    cB
    cB
    @22
    fcoi1
    3syl
    eqtr2d
    @22
    @23
    @25
    coass
    syl6eqr
    @21
    @26
    @29
    @23
    ccom
    #
    @25
    ccom
    #
    @29
    @21
    @24
    @47
    @25
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
    cdlemk54
    coeq1d
    @21
    @48
    @29
    @30
    ccom
    #
    @29
    @29
    @23
    @25
    coass
    @21
    @49
    @29
    @4
    ccom
    #
    @29
    @21
    @30
    @4
    @29
    @41
    coeq2d
    @21
    cB
    cB
    @29
    wf1o
    #
    cB
    cB
    @29
    wf
    @50
    @29
    wceq
    @21
    @0
    @29
    cT
    wcel
    #
    @51
    @35
    @21
    @0
    @27
    cT
    wcel
    #
    @28
    cT
    wcel
    #
    @52
    @35
    @21
    @0
    @36
    @8
    @6
    @37
    @53
    @35
    @38
    @45
    @39
    @40
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
    cdlemk35s-id
    syl131anc
    @21
    @0
    @36
    @11
    @6
    @37
    @54
    @35
    @38
    @46
    @39
    @40
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
    syl131anc
    cT
    @27
    @28
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    ltrnco
    syl3anc
    cB
    cT
    @29
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
    @29
    f1of
    cB
    cB
    @29
    fcoi1
    3syl
    eqtrd
    syl5eq
    eqtrd
    eqtrd
end
