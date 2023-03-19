include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "crio.mm"
include "w3a.mm"
include "wrex.mm"
include "cdlemg1cex.mm"
include "simplll.mm"
include "simpllr.mm"
include "simplrl.mm"
include "simprl.mm"
include "simplrr.mm"
include "simprr.mm"
include "eqid.mm"
include "cdlemg1b2.mm"
include "syl222anc.mm"
include "eqeq2d.mm"
include "pm5.32da.mm"
include "df-3an.mm"
include "3bitr4g.mm"
include "2rexbidva.mm"
include "bitrd.mm"

theorem cdlemg2cex
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vs: setvar s
  let vq: setvar q
  let vp: setvar p
  let vf: setvar f
  let cP: class P
  let cQ: class Q
  let cX: class X
  assume cdlemg2.b: |- B = ( Base ` K )
  assume cdlemg2.l: |- .<_ = ( le ` K )
  assume cdlemg2.j: |- .\/ = ( join ` K )
  assume cdlemg2.m: |- ./\ = ( meet ` K )
  assume cdlemg2.a: |- A = ( Atoms ` K )
  assume cdlemg2.h: |- H = ( LHyp ` K )
  assume cdlemg2.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2ex.u: |- U = ( ( p .\/ q ) ./\ W )
  assume cdlemg2ex.d: |- D = ( ( t .\/ U ) ./\ ( q .\/ ( ( p .\/ t ) ./\ W ) ) )
  assume cdlemg2ex.e: |- E = ( ( p .\/ q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemg2ex.g: |- G = ( x e. B |-> if ( ( p =/= q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( p .\/ q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( p .\/ q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint F p
  disjoint F q
  disjoint H p
  disjoint H q
  disjoint K p
  disjoint K q
  disjoint .<_ p
  disjoint .<_ q
  disjoint T p
  disjoint T q
  disjoint W p
  disjoint W q
  disjoint p s
  disjoint p t
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q s
  disjoint q t
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D s
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint U s
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint f p
  disjoint f q
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint D f
  disjoint E f
  disjoint .\/ f
  disjoint ./\ f
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint F f
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint A f
  disjoint H f
  disjoint K f
  disjoint .<_ f
  disjoint P f
  disjoint Q f
  disjoint T f
  disjoint W f
  disjoint G f
  assert |- ( ( K e. HL /\ W e. H ) -> ( F e. T <-> E. p e. A E. q e. A ( -. p .<_ W /\ -. q .<_ W /\ F = G ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cF
    cT
    wcel
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cF
    @3
    vf
    cv
    cfv
    @5
    wceq
    vf
    cT
    crio
    #
    wceq
    #
    w3a
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    @4
    @6
    cF
    cG
    wceq
    #
    w3a
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    cA
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    vq
    vp
    cdlemg2.l
    cdlemg2.a
    cdlemg2.h
    cdlemg2.t
    cdlemg1cex
    @2
    @9
    @11
    vp
    vq
    cA
    cA
    @2
    @3
    cA
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    wa
    #
    @4
    @6
    wa
    #
    @8
    wa
    @16
    @10
    wa
    @9
    @11
    @15
    @16
    @8
    @10
    @15
    @16
    wa
    #
    @7
    cG
    cF
    @17
    @0
    @1
    @12
    @4
    @13
    @6
    @7
    cG
    wceq
    @0
    @1
    @14
    @16
    simplll
    @0
    @1
    @14
    @16
    simpllr
    @2
    @12
    @13
    @16
    simplrl
    @15
    @4
    @6
    simprl
    @2
    @12
    @13
    @16
    simplrr
    @15
    @4
    @6
    simprr
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    @3
    @5
    cT
    cU
    vf
    cE
    @7
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    cdlemg2.b
    cdlemg2.l
    cdlemg2.j
    cdlemg2.m
    cdlemg2.a
    cdlemg2.h
    cdlemg2ex.u
    cdlemg2ex.d
    cdlemg2ex.e
    cdlemg2ex.g
    cdlemg2.t
    @7
    eqid
    cdlemg1b2
    syl222anc
    eqeq2d
    pm5.32da
    @4
    @6
    @8
    df-3an
    @4
    @6
    @10
    df-3an
    3bitr4g
    2rexbidva
    bitrd
end
