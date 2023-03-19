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
include "ccnv.mm"
include "co.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp31.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "simp33.mm"
include "jca.mm"
include "simp2.mm"
include "simp32.mm"
include "cdlemk11t.mm"
include "syl312anc.mm"
include "cnvco.mm"
include "coeq2i.mm"
include "coass.mm"
include "eqtr4i.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "syl2anc.mm"
include "f1ococnv2.mm"
include "syl.mm"
include "coeq1d.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "fcoi2.mm"
include "4syl.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "trlcnv.mm"
include "oveq2d.mm"
include "breqtrd.mm"

theorem cdlemk45
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( G o. I ) =/= ( _I |` B ) ) ) -> ( [_ ( G o. I ) / g ]_ X ` P ) .<_ ( ( [_ I / g ]_ X ` P ) .\/ ( R ` G ) ) )

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
    @1
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
    cN
    cR
    cfv
    wceq
    w3a
    #
    cI
    cT
    wcel
    #
    cI
    @1
    wne
    #
    cG
    cI
    ccom
    #
    @1
    wne
    #
    w3a
    #
    w3a
    #
    cP
    vg
    @10
    cX
    csb
    cfv
    #
    cP
    vg
    cI
    cX
    csb
    cfv
    #
    cI
    @10
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    @15
    cG
    cR
    cfv
    #
    c.or
    co
    c.le
    @13
    @0
    @2
    @10
    cT
    wcel
    #
    @11
    wa
    @7
    @8
    @9
    @14
    @19
    c.le
    wbr
    @0
    @2
    @5
    @7
    @12
    simp11
    #
    @0
    @2
    @5
    @7
    @12
    simp12
    @13
    @21
    @11
    @13
    @0
    @3
    @8
    @21
    @22
    @3
    @4
    @0
    @2
    @7
    @12
    simp13l
    #
    @6
    @7
    @8
    @9
    @11
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
    syl3anc
    @6
    @7
    @8
    @9
    @11
    simp33
    jca
    @6
    @7
    @12
    simp2
    @24
    @6
    @7
    @8
    @9
    @11
    simp32
    vz
    cA
    cB
    cP
    cR
    cT
    vg
    cF
    @10
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
    cdlemk11t
    syl312anc
    @13
    @18
    @20
    @15
    c.or
    @13
    @18
    cG
    ccnv
    #
    cR
    cfv
    #
    @20
    @13
    @17
    @25
    cR
    @13
    @17
    cI
    cI
    ccnv
    #
    ccom
    #
    @25
    ccom
    #
    @25
    @17
    cI
    @27
    @25
    ccom
    #
    ccom
    @29
    @16
    @30
    cI
    cG
    cI
    cnvco
    coeq2i
    cI
    @27
    @25
    coass
    eqtr4i
    @13
    @29
    @1
    @25
    ccom
    #
    @25
    @13
    @28
    @1
    @25
    @13
    cB
    cB
    cI
    wf1o
    #
    @28
    @1
    wceq
    @13
    @0
    @8
    @32
    @22
    @24
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
    f1ococnv2
    syl
    coeq1d
    @13
    cB
    cB
    cG
    wf1o
    #
    cB
    cB
    @25
    wf1o
    cB
    cB
    @25
    wf
    @31
    @25
    wceq
    @13
    @0
    @3
    @33
    @22
    @23
    cB
    cT
    cG
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
    cG
    f1ocnv
    cB
    cB
    @25
    f1of
    cB
    cB
    @25
    fcoi2
    4syl
    eqtrd
    syl5eq
    fveq2d
    @13
    @0
    @3
    @26
    @20
    wceq
    @22
    @23
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    trlcnv
    syl2anc
    eqtrd
    oveq2d
    breqtrd
end
