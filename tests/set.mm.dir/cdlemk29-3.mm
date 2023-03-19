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
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "wreu.mm"
include "wrex.mm"
include "cdlemk28-3.mm"
include "wb.mm"
include "simp1.mm"
include "cdlemftr2.mm"
include "reusv1.mm"
include "3syl.mm"
include "mpbird.mm"
include "riotacl.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem cdlemk29-3
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let ve: setvar e
  let vf: setvar f
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
  let cW: class W
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vd: setvar d
  let cD: class D
  let cQ: class Q
  let cC: class C
  let vx: setvar x
  let va: setvar a
  assume cdlemk3.b: |- B = ( Base ` K )
  assume cdlemk3.l: |- .<_ = ( le ` K )
  assume cdlemk3.j: |- .\/ = ( join ` K )
  assume cdlemk3.m: |- ./\ = ( meet ` K )
  assume cdlemk3.a: |- A = ( Atoms ` K )
  assume cdlemk3.h: |- H = ( LHyp ` K )
  assume cdlemk3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk3.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk3.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk3.u1: |- Y = ( d e. T , e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` d ) ` P ) .\/ ( R ` ( e o. `' d ) ) ) ) ) )
  assume cdlemk3.x: |- X = ( iota_ z e. T A. b e. T ( ( b =/= ( _I |` B ) /\ ( R ` b ) =/= ( R ` F ) /\ ( R ` b ) =/= ( R ` G ) ) -> z = ( b Y G ) ) )

  disjoint d e
  disjoint d f
  disjoint d i
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint ./\ e
  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ d
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint d j
  disjoint e j
  disjoint f j
  disjoint i j
  disjoint F f
  disjoint F i
  disjoint G d
  disjoint G e
  disjoint G j
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint W d
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint b f
  disjoint b i
  disjoint ./\ j
  disjoint .<_ j
  disjoint .\/ j
  disjoint A j
  disjoint F j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint P j
  disjoint R j
  disjoint b d
  disjoint S d
  disjoint b e
  disjoint S e
  disjoint b j
  disjoint S j
  disjoint S b
  disjoint T j
  disjoint W j
  disjoint F d
  disjoint F e
  disjoint .<_ e
  disjoint G f
  disjoint G i
  disjoint .<_ b
  disjoint A b
  disjoint b z
  disjoint B b
  disjoint B z
  disjoint F b
  disjoint F z
  disjoint G b
  disjoint G z
  disjoint H b
  disjoint K b
  disjoint N b
  disjoint P b
  disjoint R b
  disjoint R z
  disjoint T b
  disjoint T z
  disjoint W b
  disjoint W z
  disjoint Y b
  disjoint Y z
  disjoint d z
  disjoint e z
  disjoint f z
  disjoint i z
  disjoint j z
  disjoint .<_ z
  disjoint A z
  disjoint H z
  disjoint K z
  disjoint N z
  disjoint P z
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D i
  disjoint D j
  disjoint Q d
  disjoint Q e
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C i
  disjoint C j
  disjoint d x
  disjoint e x
  disjoint f x
  disjoint i x
  disjoint j x
  disjoint .<_ x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint F x
  disjoint G x
  disjoint H x
  disjoint K x
  disjoint N x
  disjoint P x
  disjoint R x
  disjoint T x
  disjoint Y x
  disjoint W x
  disjoint C x
  disjoint a b
  disjoint .<_ a
  disjoint A a
  disjoint a z
  disjoint B a
  disjoint F a
  disjoint G a
  disjoint H a
  disjoint K a
  disjoint N a
  disjoint P a
  disjoint R a
  disjoint T a
  disjoint W a
  disjoint Y a
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a i
  disjoint a j
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( F e. T /\ F =/= ( _I |` B ) ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ N e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) ) -> X e. T )

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
    cG
    cT
    wcel
    cG
    @1
    wne
    wa
    cN
    cT
    wcel
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    wa
    #
    w3a
    #
    cX
    vb
    cv
    #
    @1
    wne
    @6
    cR
    cfv
    #
    @3
    wne
    @7
    cG
    cR
    cfv
    #
    wne
    w3a
    #
    vz
    cv
    @6
    cG
    cY
    co
    #
    wceq
    wi
    vb
    cT
    wral
    #
    vz
    cT
    crio
    #
    cT
    cdlemk3.x
    @5
    @11
    vz
    cT
    wreu
    #
    @12
    cT
    wcel
    @5
    @13
    @11
    vz
    cT
    wrex
    #
    vz
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
    cY
    vb
    vd
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.m
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.s
    cdlemk3.u1
    cdlemk28-3
    @5
    @0
    @9
    vb
    cT
    wrex
    @13
    @14
    wb
    @0
    @2
    @4
    simp1
    cB
    cR
    cT
    vb
    cH
    cK
    cW
    @3
    @8
    cdlemk3.b
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemftr2
    @9
    vz
    vb
    cT
    cT
    @10
    reusv1
    3syl
    mpbird
    @11
    vz
    cT
    riotacl
    syl
    syl5eqel
end
