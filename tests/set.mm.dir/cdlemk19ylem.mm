include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "csb.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3rl.mm"
include "simp3rr.mm"
include "3jca.mm"
include "cdlemkyuu.mm"
include "syl312anc.mm"
include "simp1rl.mm"
include "simp1rr.mm"
include "eqid.mm"
include "cdlemk19.mm"
include "syl313anc.mm"
include "fveq1d.mm"
include "eqtrd.mm"

theorem cdlemk19ylem
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
  let cH: class H
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
  let cG: class G
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
  disjoint F g
  disjoint ./\ g
  disjoint .\/ g
  disjoint B g
  disjoint P g
  disjoint R g
  disjoint T g
  disjoint Z g
  disjoint b g
  disjoint d g
  disjoint d e
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint ./\ d
  disjoint .\/ d
  disjoint G g
  disjoint G d
  disjoint G e
  disjoint G j
  disjoint P d
  disjoint R d
  disjoint b d
  disjoint S d
  disjoint T d
  disjoint W d
  disjoint I e
  disjoint I g
  disjoint I j
  disjoint G g
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ F =/= ( _I |` B ) ) ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( b e. T /\ ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) ) ) ) -> [_ F / g ]_ Y = ( N ` P ) )

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
    wa
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
    #
    cN
    cR
    cfv
    wceq
    w3a
    #
    vb
    cv
    #
    cT
    wcel
    #
    @8
    @2
    wne
    #
    @8
    cR
    cfv
    @6
    wne
    #
    wa
    #
    wa
    #
    w3a
    #
    vg
    cF
    cY
    csb
    #
    cP
    cF
    cC
    cfv
    #
    cfv
    #
    cP
    cN
    cfv
    @14
    @0
    @4
    @4
    @7
    @9
    @10
    @11
    @11
    w3a
    @15
    @17
    wceq
    @0
    @4
    @7
    @13
    simp1l
    #
    @0
    @4
    @7
    @13
    simp1r
    #
    @19
    @5
    @7
    @13
    simp2
    #
    @5
    @7
    @9
    @12
    simp3l
    #
    @14
    @10
    @11
    @11
    @10
    @11
    @9
    @5
    @7
    simp3rl
    #
    @10
    @11
    @9
    @5
    @7
    simp3rr
    #
    @23
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
    cF
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
    @14
    cP
    @16
    cN
    @14
    @0
    @1
    @9
    @7
    @3
    @10
    @11
    @16
    cN
    wceq
    @18
    @1
    @3
    @0
    @7
    @13
    simp1rl
    @21
    @20
    @1
    @3
    @0
    @7
    @13
    simp1rr
    @22
    @23
    cA
    cB
    @8
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
    cH
    c.or
    cK
    c.le
    c.an
    cN
    @8
    cS
    cfv
    #
    cW
    cdlemk5.b
    cdlemk5.l
    cdlemk5.j
    cdlemk5.m
    cdlemk5.a
    cdlemk5.h
    cdlemk5.t
    cdlemk5.r
    cdlemk5c.s
    @24
    eqid
    cdlemk5a.u2
    cdlemk19
    syl313anc
    fveq1d
    eqtrd
end
