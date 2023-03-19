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
include "wrex.mm"
include "co.mm"
include "cdlemftr2.mm"
include "3ad2ant1.mm"
include "nfv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfbr.mm"
include "simpl1.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpr.mm"
include "cdlemk37.mm"
include "syl331anc.mm"
include "exp32.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem cdlemk38
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> ( X ` P ) .<_ ( P .\/ ( R ` G ) ) )

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
    wa
    #
    w3a
    #
    vb
    cv
    #
    @1
    wne
    @11
    cR
    cfv
    #
    @7
    wne
    @12
    cG
    cR
    cfv
    #
    wne
    w3a
    #
    vb
    cT
    wrex
    #
    cP
    cX
    cfv
    #
    cP
    @13
    c.or
    co
    #
    c.le
    wbr
    #
    @0
    @5
    @15
    @9
    cB
    cR
    cT
    vb
    cH
    cK
    cW
    @7
    @13
    cdlemk4.b
    cdlemk4.h
    cdlemk4.t
    cdlemk4.r
    cdlemftr2
    3ad2ant1
    @10
    @14
    @18
    vb
    cT
    @10
    vb
    nfv
    vb
    @16
    @17
    c.le
    vb
    cP
    cX
    vb
    cX
    @14
    cP
    vz
    cv
    cfv
    cY
    wceq
    wi
    #
    vb
    cT
    wral
    #
    vz
    cT
    crio
    cdlemk4.x
    @20
    vb
    vz
    cT
    @19
    vb
    cT
    nfra1
    vb
    cT
    nfcv
    nfriota
    nfcxfr
    vb
    cP
    nfcv
    nffv
    vb
    c.le
    nfcv
    vb
    @17
    nfcv
    nfbr
    @10
    @11
    cT
    wcel
    #
    @14
    @18
    @10
    @21
    @14
    wa
    #
    wa
    @0
    @2
    @3
    @4
    @6
    @8
    @22
    @18
    @0
    @5
    @9
    @22
    simpl1
    @2
    @3
    @4
    @0
    @9
    @22
    simpl21
    @2
    @3
    @4
    @0
    @9
    @22
    simpl22
    @2
    @3
    @4
    @0
    @9
    @22
    simpl23
    @6
    @8
    @0
    @5
    @22
    simpl3l
    @6
    @8
    @0
    @5
    @22
    simpl3r
    @10
    @22
    simpr
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
    cdlemk37
    syl331anc
    exp32
    rexlimd
    mpd
end
