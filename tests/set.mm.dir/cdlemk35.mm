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
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "crio.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "wi.mm"
include "wral.mm"
include "eqid.mm"
include "cdlemk34.mm"
include "wb.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "eqeq2i.mm"
include "imbi2i.mm"
include "ralbii.mm"
include "a1i.mm"
include "riotabiia.mm"
include "syl6eqr.mm"
include "cdlemk29-3.mm"
include "eqeltrrd.mm"

theorem cdlemk35
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> X e. T )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
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
    cG
    cT
    wcel
    cG
    @0
    wne
    wa
    cN
    cT
    wcel
    w3a
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
    wa
    w3a
    #
    vb
    cv
    #
    @0
    wne
    @3
    cR
    cfv
    #
    @1
    wne
    @4
    cG
    cR
    cfv
    #
    wne
    w3a
    #
    vz
    cv
    #
    @3
    cG
    vd
    ve
    cT
    cT
    cP
    vj
    cv
    cfv
    cP
    ve
    cv
    #
    cR
    cfv
    c.or
    co
    cP
    vd
    cv
    #
    vf
    cT
    cP
    vi
    cv
    cfv
    cP
    vf
    cv
    #
    cR
    cfv
    c.or
    co
    cP
    cN
    cfv
    #
    @10
    cF
    ccnv
    #
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    vi
    cT
    crio
    cmpt
    #
    cfv
    cfv
    @8
    @9
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    vj
    cT
    crio
    cmpt2
    #
    co
    wceq
    wi
    vb
    cT
    wral
    vz
    cT
    crio
    #
    cX
    cT
    @2
    @15
    @6
    cP
    @7
    cfv
    #
    cP
    @5
    c.or
    co
    #
    cP
    @4
    c.or
    co
    @11
    @3
    @12
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    cG
    @3
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
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
    vz
    cA
    cB
    cP
    cR
    @13
    cT
    ve
    vf
    vi
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    @15
    @14
    vb
    vd
    cdlemk4.b
    cdlemk4.l
    cdlemk4.j
    cdlemk4.m
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    @13
    eqid
    #
    @14
    eqid
    #
    @15
    eqid
    #
    cdlemk34
    cX
    @6
    @16
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
    @25
    cdlemk4.x
    @31
    @24
    vz
    cT
    @31
    @24
    wb
    @7
    cT
    wcel
    @30
    @23
    vb
    cT
    @29
    @22
    @6
    cY
    @21
    @16
    cY
    @17
    cZ
    @19
    c.or
    co
    #
    c.an
    co
    @21
    cdlemk4.y
    @32
    @20
    @17
    c.an
    cZ
    @18
    @19
    c.or
    cdlemk4.z
    oveq1i
    oveq2i
    eqtri
    eqeq2i
    imbi2i
    ralbii
    a1i
    riotabiia
    eqtri
    syl6eqr
    vz
    cA
    cB
    cP
    cR
    @13
    cT
    ve
    vf
    vi
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    @15
    @14
    vb
    vd
    cdlemk4.b
    cdlemk4.l
    cdlemk4.j
    cdlemk4.m
    cdlemk4.a
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    @26
    @27
    @28
    cdlemk29-3
    eqeltrrd
end
