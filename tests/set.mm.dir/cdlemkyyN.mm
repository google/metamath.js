include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "csb.mm"
include "simp11.mm"
include "simp12.mm"
include "jca.mm"
include "simp13.mm"
include "simp211.mm"
include "simp3l.mm"
include "simp213.mm"
include "simp3r2.mm"
include "simp212.mm"
include "simp3r1.mm"
include "simp23.mm"
include "cdlemk30.mm"
include "syl233anc.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3jca.mm"
include "simp22l.mm"
include "simp3r3.mm"
include "simp22r.mm"
include "cdlemk31.mm"
include "syl223anc.mm"
include "simp22.mm"
include "simp3.mm"
include "cdlemk42yN.mm"
include "syl331anc.mm"
include "3eqtr4rd.mm"

theorem cdlemkyyN
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vd: setvar d
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
  assume cdlemk5a.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk5a.u1: |- V = ( d e. T , e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` d ) ` P ) .\/ ( R ` ( e o. `' d ) ) ) ) ) )

  disjoint d e
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint e j
  disjoint ./\ e
  disjoint f i
  disjoint f j
  disjoint ./\ f
  disjoint i j
  disjoint ./\ i
  disjoint ./\ j
  disjoint .<_ i
  disjoint .<_ j
  disjoint .\/ d
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint .\/ j
  disjoint A i
  disjoint A j
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint G d
  disjoint G e
  disjoint G j
  disjoint H i
  disjoint H j
  disjoint K i
  disjoint K j
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
  disjoint b d
  disjoint b e
  disjoint b j
  disjoint S b
  disjoint S d
  disjoint S e
  disjoint S j
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
  disjoint b f
  disjoint b i
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
  disjoint b j
  disjoint g j
  disjoint j z
  disjoint .<_ j
  disjoint A j
  disjoint B j
  disjoint F j
  disjoint G j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint P j
  disjoint R j
  disjoint T j
  disjoint W j
  disjoint X j
  disjoint I b
  disjoint I g
  disjoint I z
  disjoint I j
  assert |- ( ( ( K e. HL /\ W e. H /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ F =/= ( _I |` B ) /\ N e. T ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) ) ) -> ( [_ G / g ]_ X ` P ) = ( ( b V G ) ` P ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
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
    cG
    @6
    wne
    #
    wa
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
    vb
    cv
    #
    cT
    wcel
    #
    @15
    @6
    wne
    #
    @15
    cR
    cfv
    #
    @2
    wne
    #
    @18
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
    @20
    c.or
    co
    #
    cP
    @15
    cS
    cfv
    cfv
    #
    cG
    @15
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
    @25
    cZ
    @27
    c.or
    co
    #
    c.an
    co
    #
    cP
    @15
    cG
    cV
    co
    cfv
    #
    cP
    vg
    cG
    cX
    csb
    cfv
    #
    @24
    @28
    @30
    @25
    c.an
    @24
    @26
    cZ
    @27
    c.or
    @24
    @26
    cP
    @18
    c.or
    co
    cP
    cN
    cfv
    @15
    cF
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    cZ
    @24
    @0
    @1
    wa
    #
    @3
    @5
    @16
    @8
    @19
    @7
    @17
    wa
    @13
    @26
    @34
    wceq
    @24
    @0
    @1
    @0
    @1
    @3
    @14
    @23
    simp11
    @0
    @1
    @3
    @14
    @23
    simp12
    jca
    #
    @0
    @1
    @3
    @14
    @23
    simp13
    #
    @5
    @7
    @8
    @12
    @13
    @4
    @23
    simp211
    #
    @4
    @14
    @16
    @22
    simp3l
    #
    @5
    @7
    @8
    @12
    @13
    @4
    @23
    simp213
    #
    @17
    @19
    @21
    @16
    @4
    @14
    simp3r2
    #
    @24
    @7
    @17
    @5
    @7
    @8
    @12
    @13
    @4
    @23
    simp212
    #
    @17
    @19
    @21
    @16
    @4
    @14
    simp3r1
    #
    jca
    @4
    @9
    @12
    @13
    @23
    simp23
    #
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    vb
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5a.s
    cdlemk30
    syl233anc
    cdlemk5.z
    syl6eqr
    oveq1d
    oveq2d
    @24
    @35
    @3
    @5
    @16
    @8
    w3a
    @10
    @19
    @21
    wa
    @7
    @17
    @11
    w3a
    @13
    @32
    @29
    wceq
    @36
    @37
    @24
    @5
    @16
    @8
    @38
    @39
    @40
    3jca
    @10
    @11
    @9
    @13
    @4
    @23
    simp22l
    @24
    @19
    @21
    @41
    @17
    @19
    @21
    @16
    @4
    @14
    simp3r3
    jca
    @24
    @7
    @17
    @11
    @42
    @43
    @10
    @11
    @9
    @13
    @4
    @23
    simp22r
    3jca
    @44
    cA
    cB
    cP
    cR
    cS
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
    cV
    vb
    vd
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5a.s
    cdlemk5a.u1
    cdlemk31
    syl223anc
    @24
    @35
    @5
    @7
    wa
    @12
    @8
    @13
    @3
    @23
    @33
    @31
    wceq
    @36
    @24
    @5
    @7
    @38
    @42
    jca
    @4
    @9
    @12
    @13
    @23
    simp22
    @40
    @44
    @37
    @4
    @14
    @23
    simp3
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
    cdlemk42yN
    syl331anc
    3eqtr4rd
end
