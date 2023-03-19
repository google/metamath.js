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
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "eqcomi.mm"
include "wreu.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "cdlemk35.mm"
include "syl132anc.mm"
include "syl5eqelr.mm"
include "cltrn.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "riotaclbBAD.mm"
include "sylibr.mm"
include "nfriota1.mm"
include "nfcxfr.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffv.mm"
include "nfeq1.mm"
include "nfim.mm"
include "nfral.mm"
include "nfra1.mm"
include "nfriota.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "ralbid.mm"
include "riota2f.mm"
include "syl2anc.mm"
include "mpbiri.mm"
include "rsp.mm"
include "syl.mm"
include "impd.mm"
include "3impia.mm"

theorem cdlemk36
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cT: class T
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
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  assume cdlemk4.b: |- B = ( Base ` K )
  assume cdlemk4.l: |- .<_ = ( le ` K )
  assume cdlemk4.j: |- .\/ = ( join ` K )
  assume cdlemk4.m: |- ./\ = ( meet ` K )
  assume cdlemk4.a: |- A = ( Atoms ` K )
  assume cdlemk4.h: |- H = ( LHyp ` K )
  assume cdlemk4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk4.z: |- Z = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) )
  assume cdlemk4.y: |- Y = ( ( P .\/ ( R ` G ) ) ./\ ( Z .\/ ( R ` ( G o. `' b ) ) ) )
  assume cdlemk4.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> ( z ` P ) = Y ) )

  disjoint b z
  disjoint ./\ b
  disjoint ./\ z
  disjoint .<_ b
  disjoint .<_ z
  disjoint .\/ b
  disjoint .\/ z
  disjoint A b
  disjoint A z
  disjoint B b
  disjoint B z
  disjoint F b
  disjoint F z
  disjoint G b
  disjoint G z
  disjoint H b
  disjoint H z
  disjoint K b
  disjoint K z
  disjoint N b
  disjoint N z
  disjoint P b
  disjoint P z
  disjoint R b
  disjoint R z
  disjoint T b
  disjoint T z
  disjoint W b
  disjoint W z
  disjoint Y z
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b i
  disjoint b j
  disjoint d e
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint d z
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint e j
  disjoint e z
  disjoint ./\ e
  disjoint f i
  disjoint f j
  disjoint f z
  disjoint ./\ f
  disjoint i j
  disjoint i z
  disjoint ./\ i
  disjoint j z
  disjoint ./\ j
  disjoint .<_ e
  disjoint .<_ i
  disjoint .<_ j
  disjoint .\/ d
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint .\/ j
  disjoint A i
  disjoint A j
  disjoint F d
  disjoint F e
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint G d
  disjoint G e
  disjoint G f
  disjoint G i
  disjoint G j
  disjoint H i
  disjoint H j
  disjoint K i
  disjoint K j
  disjoint N d
  disjoint N e
  disjoint N f
  disjoint N i
  disjoint N j
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint P j
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint T j
  disjoint W d
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint W j
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) ) ) -> ( X ` P ) = Y )

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
    cG
    @1
    wne
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
    #
    cN
    cR
    cfv
    wceq
    #
    w3a
    #
    vb
    cv
    #
    cT
    wcel
    #
    @10
    @1
    wne
    @10
    cR
    cfv
    #
    @7
    wne
    @12
    cG
    cR
    cfv
    wne
    w3a
    #
    wa
    cP
    cX
    cfv
    #
    cY
    wceq
    #
    @4
    @9
    wa
    #
    @11
    @13
    @15
    @16
    @13
    @15
    wi
    #
    vb
    cT
    wral
    #
    @11
    @17
    wi
    @16
    @18
    @13
    cP
    vz
    cv
    #
    cfv
    #
    cY
    wceq
    #
    wi
    #
    vb
    cT
    wral
    #
    vz
    cT
    crio
    #
    cX
    wceq
    #
    cX
    @24
    cdlemk4.x
    eqcomi
    @16
    cX
    cT
    wcel
    #
    @23
    vz
    cT
    wreu
    #
    @18
    @25
    wb
    @16
    @0
    @2
    @3
    @5
    @6
    @8
    @26
    @0
    @2
    @3
    @9
    simpl1
    @0
    @2
    @3
    @9
    simpl2
    @0
    @2
    @3
    @9
    simpl3
    @4
    @5
    @6
    @8
    simpr1
    @4
    @5
    @6
    @8
    simpr2
    @4
    @5
    @6
    @8
    simpr3
    vz
    cA
    cB
    cP
    cR
    cT
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
    cdlemk4.b
    cdlemk4.l
    cdlemk4.j
    cdlemk4.m
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    cdlemk4.z
    cdlemk4.y
    cdlemk4.x
    cdlemk35
    syl132anc
    #
    @16
    @24
    cT
    wcel
    @27
    @16
    @24
    cX
    cT
    cdlemk4.x
    @28
    syl5eqelr
    @23
    vz
    cT
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    cdlemk4.t
    cW
    @29
    fvex
    eqeltri
    riotaclbBAD
    sylibr
    @23
    @18
    vz
    cT
    cX
    vz
    cX
    @24
    cdlemk4.x
    @23
    vz
    cT
    nfriota1
    nfcxfr
    #
    @17
    vz
    vb
    cT
    vz
    cT
    nfcv
    @13
    @15
    vz
    @13
    vz
    nfv
    vz
    @14
    cY
    vz
    cP
    cX
    @30
    vz
    cP
    nfcv
    nffv
    nfeq1
    nfim
    nfral
    @19
    cX
    wceq
    #
    @22
    @17
    vb
    cT
    vb
    @19
    cX
    vb
    cX
    @24
    cdlemk4.x
    @23
    vb
    vz
    cT
    @22
    vb
    cT
    nfra1
    vb
    cT
    nfcv
    nfriota
    nfcxfr
    nfeq2
    @31
    @21
    @15
    @13
    @31
    @20
    @14
    cY
    cP
    @19
    cX
    fveq1
    eqeq1d
    imbi2d
    ralbid
    riota2f
    syl2anc
    mpbiri
    @17
    vb
    cT
    rsp
    syl
    impd
    3impia
end
