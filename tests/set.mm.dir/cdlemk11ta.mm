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
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "csb.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp31.mm"
include "simp21.mm"
include "simp13l.mm"
include "simp331.mm"
include "3jca.mm"
include "simp22.mm"
include "simp23.mm"
include "simp12r.mm"
include "simp321.mm"
include "simp13r.mm"
include "simp332.mm"
include "simp322.mm"
include "simp323.mm"
include "necomd.mm"
include "simp333.mm"
include "eqid.mm"
include "cdlemk11u.mm"
include "syl333anc.mm"
include "simp32.mm"
include "jca.mm"
include "cdlemkyuu.mm"
include "syld3an3.mm"
include "simp12.mm"
include "simp2.mm"
include "syl312anc.mm"
include "oveq1d.mm"
include "3brtr4d.mm"

theorem cdlemk11ta
  let cA: class A
  let cB: class B
  let cC: class C
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
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
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
  assume cdlemk5c.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk5a.u2: |- C = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` b ) ` P ) .\/ ( R ` ( e o. `' b ) ) ) ) ) )

  disjoint e g
  disjoint f g
  disjoint g i
  disjoint g j
  disjoint ./\ g
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
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint P j
  disjoint R g
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint R j
  disjoint b e
  disjoint b j
  disjoint S b
  disjoint S e
  disjoint S j
  disjoint T g
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint T j
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint W j
  disjoint Z g
  disjoint b g
  disjoint b f
  disjoint b i
  disjoint F e
  disjoint I e
  disjoint I g
  disjoint I j
  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint G g
  disjoint d g
  disjoint d e
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint ./\ d
  disjoint .\/ d
  disjoint G d
  disjoint P d
  disjoint R d
  disjoint b d
  disjoint S d
  disjoint T d
  disjoint W d
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) /\ ( I e. T /\ I =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` I ) ) ) ) -> [_ G / g ]_ Y .<_ ( [_ I / g ]_ Y .\/ ( R ` ( I o. `' G ) ) ) )

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
    cI
    cT
    wcel
    #
    cI
    @2
    wne
    #
    @17
    cI
    cR
    cfv
    #
    wne
    #
    w3a
    #
    w3a
    #
    w3a
    #
    cP
    cG
    cC
    cfv
    cfv
    #
    cP
    cI
    cC
    cfv
    cfv
    #
    cI
    cG
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    vg
    cG
    cY
    csb
    #
    vg
    cI
    cY
    csb
    #
    @31
    c.or
    co
    c.le
    @28
    @0
    @1
    @15
    @9
    @5
    @22
    w3a
    @10
    @12
    @3
    @16
    @6
    w3a
    @23
    @18
    @19
    @17
    wne
    #
    @24
    @17
    wne
    #
    w3a
    @29
    @32
    c.le
    wbr
    @0
    @4
    @7
    @13
    @27
    simp11
    #
    @1
    @3
    @0
    @7
    @13
    @27
    simp12l
    @8
    @13
    @15
    @21
    @26
    simp31
    #
    @28
    @9
    @5
    @22
    @8
    @9
    @10
    @12
    @27
    simp21
    @5
    @6
    @0
    @4
    @13
    @27
    simp13l
    @22
    @23
    @25
    @15
    @21
    @8
    @13
    simp331
    #
    3jca
    @8
    @9
    @10
    @12
    @27
    simp22
    @8
    @9
    @10
    @12
    @27
    simp23
    @28
    @3
    @16
    @6
    @1
    @3
    @0
    @7
    @13
    @27
    simp12r
    @16
    @18
    @20
    @15
    @26
    @8
    @13
    simp321
    #
    @5
    @6
    @0
    @4
    @13
    @27
    simp13r
    3jca
    @22
    @23
    @25
    @15
    @21
    @8
    @13
    simp332
    #
    @28
    @18
    @35
    @36
    @16
    @18
    @20
    @15
    @26
    @8
    @13
    simp322
    #
    @28
    @17
    @19
    @16
    @18
    @20
    @15
    @26
    @8
    @13
    simp323
    necomd
    @28
    @17
    @24
    @22
    @23
    @25
    @15
    @21
    @8
    @13
    simp333
    #
    necomd
    3jca
    cA
    cB
    @14
    cP
    cR
    cS
    cT
    cC
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
    @14
    cS
    cfv
    #
    cP
    cG
    cfv
    cP
    cI
    cfv
    c.or
    co
    cG
    @14
    ccnv
    #
    ccom
    cR
    cfv
    cI
    @45
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    cW
    cI
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5c.s
    @44
    eqid
    cdlemk5a.u2
    @46
    eqid
    cdlemk11u
    syl333anc
    @8
    @13
    @27
    @15
    @21
    wa
    @33
    @29
    wceq
    @28
    @15
    @21
    @38
    @8
    @13
    @15
    @21
    @26
    simp32
    jca
    cA
    cB
    cC
    cP
    cR
    cS
    cT
    ve
    vf
    vg
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
    cdlemk5c.s
    cdlemk5a.u2
    cdlemkyuu
    syld3an3
    @28
    @34
    @30
    @31
    c.or
    @28
    @0
    @4
    @22
    @23
    wa
    @13
    @15
    @16
    @18
    @25
    w3a
    @34
    @30
    wceq
    @37
    @0
    @4
    @7
    @13
    @27
    simp12
    @28
    @22
    @23
    @39
    @41
    jca
    @8
    @13
    @27
    simp2
    @38
    @28
    @16
    @18
    @25
    @40
    @42
    @43
    3jca
    cA
    cB
    cC
    cP
    cR
    cS
    cT
    ve
    vf
    vg
    vi
    vj
    cF
    cI
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
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
    cdlemk5c.s
    cdlemk5a.u2
    cdlemkyuu
    syl312anc
    oveq1d
    3brtr4d
end
