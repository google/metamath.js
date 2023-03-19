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
include "csb.mm"
include "simp11.mm"
include "simp23.mm"
include "simp12l.mm"
include "simp3l.mm"
include "simp21.mm"
include "simp3r2.mm"
include "simp12r.mm"
include "simp3r1.mm"
include "jca.mm"
include "simp22.mm"
include "cdlemk30.mm"
include "syl233anc.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3jca.mm"
include "simp13l.mm"
include "simp3r3.mm"
include "simp13r.mm"
include "cdlemk31.mm"
include "syl223anc.mm"
include "cdlemk41.mm"
include "syl.mm"
include "3eqtr4rd.mm"

theorem cdlemky
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
  let cY: class Y
  let cZ: class Z
  let vb: setvar b
  let vd: setvar d
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
  assume cdlemk5b.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk5b.u1: |- V = ( d e. T , e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` d ) ` P ) .\/ ( R ` ( e o. `' d ) ) ) ) ) )

  disjoint d g
  disjoint e g
  disjoint f g
  disjoint g i
  disjoint g j
  disjoint ./\ g
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
  disjoint .\/ g
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
  disjoint G g
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
  disjoint P g
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint P j
  disjoint R g
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
  disjoint T g
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
  disjoint Z g
  disjoint b g
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) ) ) -> [_ G / g ]_ Y = ( ( b V G ) ` P ) )

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
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    wa
    #
    cG
    cT
    wcel
    #
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
    @14
    @2
    wne
    #
    @14
    cR
    cfv
    #
    @11
    wne
    #
    @17
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
    @19
    c.or
    co
    #
    cP
    @14
    cS
    cfv
    cfv
    #
    cG
    @14
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
    @24
    cZ
    @26
    c.or
    co
    #
    c.an
    co
    #
    cP
    @14
    cG
    cV
    co
    cfv
    #
    vg
    cG
    cY
    csb
    #
    @23
    @27
    @29
    @24
    c.an
    @23
    @25
    cZ
    @26
    c.or
    @23
    @25
    cP
    @17
    c.or
    co
    cP
    cN
    cfv
    @14
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
    @23
    @0
    @12
    @1
    @15
    @9
    @18
    @3
    @16
    wa
    @10
    @25
    @33
    wceq
    @0
    @4
    @7
    @13
    @22
    simp11
    #
    @8
    @9
    @10
    @12
    @22
    simp23
    #
    @1
    @3
    @0
    @7
    @13
    @22
    simp12l
    #
    @8
    @13
    @15
    @21
    simp3l
    #
    @8
    @9
    @10
    @12
    @22
    simp21
    #
    @16
    @18
    @20
    @15
    @8
    @13
    simp3r2
    #
    @23
    @3
    @16
    @1
    @3
    @0
    @7
    @13
    @22
    simp12r
    #
    @16
    @18
    @20
    @15
    @8
    @13
    simp3r1
    #
    jca
    @8
    @9
    @10
    @12
    @22
    simp22
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
    cdlemk5b.s
    cdlemk30
    syl233anc
    cdlemk5.z
    syl6eqr
    oveq1d
    oveq2d
    @23
    @0
    @12
    @1
    @15
    @9
    w3a
    @5
    @18
    @20
    wa
    @3
    @16
    @6
    w3a
    @10
    @31
    @28
    wceq
    @34
    @35
    @23
    @1
    @15
    @9
    @36
    @37
    @38
    3jca
    @5
    @6
    @0
    @4
    @13
    @22
    simp13l
    #
    @23
    @18
    @20
    @39
    @16
    @18
    @20
    @15
    @8
    @13
    simp3r3
    jca
    @23
    @3
    @16
    @6
    @40
    @41
    @5
    @6
    @0
    @4
    @13
    @22
    simp13r
    3jca
    @42
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
    cdlemk5b.s
    cdlemk5b.u1
    cdlemk31
    syl223anc
    @23
    @5
    @32
    @30
    wceq
    @43
    cP
    cR
    cT
    vg
    cG
    c.or
    c.an
    cY
    cZ
    vb
    cdlemk5.y
    cdlemk41
    syl
    3eqtr4rd
end
