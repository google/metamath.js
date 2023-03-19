include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "cv.mm"
include "csb.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "cvv.mm"
include "vex.mm"
include "eqid.mm"
include "cdleme31sc.mm"
include "ax-mp.mm"
include "cdleme42mgN.mm"
include "cdlemg2ce.mm"
include "3com23.mm"

theorem cdlemg2jlemOLDN
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
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
  disjoint .\/ p
  disjoint .\/ q
  disjoint P p
  disjoint P q
  disjoint Q p
  disjoint Q q
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
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ F e. T ) -> ( F ` ( P .\/ Q ) ) = ( ( F ` P ) .\/ ( F ` Q ) ) )

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
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    wa
    #
    cP
    cQ
    c.or
    co
    #
    cF
    cfv
    #
    cP
    cF
    cfv
    #
    cQ
    cF
    cfv
    #
    c.or
    co
    #
    wceq
    #
    @0
    @6
    @1
    cG
    cfv
    #
    cP
    cG
    cfv
    #
    cQ
    cG
    cfv
    #
    c.or
    co
    #
    wceq
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cT
    cU
    cE
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    vq
    vp
    cdlemg2.b
    cdlemg2.l
    cdlemg2.j
    cdlemg2.m
    cdlemg2.a
    cdlemg2.h
    cdlemg2.t
    cdlemg2ex.u
    cdlemg2ex.d
    cdlemg2ex.e
    cdlemg2ex.g
    cF
    cG
    wceq
    #
    @2
    @7
    @5
    @10
    @1
    cF
    cG
    fveq1
    @11
    @3
    @8
    @4
    @9
    c.or
    cP
    cF
    cG
    fveq1
    cQ
    cF
    cG
    fveq1
    oveq12d
    eqeq12d
    vx
    vy
    vz
    vt
    cA
    cB
    vt
    vs
    cv
    #
    cD
    csb
    #
    vp
    cv
    #
    vq
    cv
    #
    cP
    cQ
    cU
    cD
    cG
    cE
    cH
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @16
    @14
    @15
    c.or
    co
    #
    c.le
    wbr
    wn
    wa
    vy
    cv
    cE
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    #
    c.or
    cK
    c.le
    c.an
    @12
    @17
    c.le
    wbr
    @18
    @13
    cif
    #
    @12
    cW
    c.le
    wbr
    wn
    @12
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @20
    wceq
    wa
    vz
    cv
    @19
    @21
    c.or
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    #
    cW
    vs
    cdlemg2.b
    cdlemg2.l
    cdlemg2.j
    cdlemg2.m
    cdlemg2.a
    cdlemg2.h
    cdlemg2ex.u
    @12
    cvv
    wcel
    @13
    @12
    cU
    c.or
    co
    @15
    @14
    @12
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    wceq
    vs
    vex
    cvv
    cD
    @14
    @15
    @12
    cU
    c.or
    c.an
    cW
    @23
    vt
    cdlemg2ex.d
    @23
    eqid
    cdleme31sc
    ax-mp
    cdlemg2ex.d
    cdlemg2ex.e
    @18
    eqid
    @19
    eqid
    @22
    eqid
    cdlemg2ex.g
    cdleme42mgN
    cdlemg2ce
    3com23
end
