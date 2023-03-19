include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "crio.mm"
include "cdleme50ltrn.mm"
include "simpll1.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "simpll2.mm"
include "simpr.mm"
include "cdleme17d.mm"
include "eqtr4d.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "ex.mm"
include "adantr.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"
include "riota5.mm"
include "eqcomd.mm"

theorem cdlemg1a
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
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vs: setvar s
  let cR: class R
  let cX: class X
  assume cdlemg1.b: |- B = ( Base ` K )
  assume cdlemg1.l: |- .<_ = ( le ` K )
  assume cdlemg1.j: |- .\/ = ( join ` K )
  assume cdlemg1.m: |- ./\ = ( meet ` K )
  assume cdlemg1.a: |- A = ( Atoms ` K )
  assume cdlemg1.h: |- H = ( LHyp ` K )
  assume cdlemg1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemg1.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemg1.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemg1.g: |- G = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )
  assume cdlemg1.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint G f
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
  disjoint f s
  disjoint f t
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D f
  disjoint D s
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E f
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint .\/ f
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
  disjoint ./\ f
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
  disjoint A f
  disjoint H f
  disjoint K f
  disjoint .<_ f
  disjoint P f
  disjoint Q f
  disjoint T f
  disjoint W f
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) -> G = ( iota_ f e. T ( f ` P ) = Q ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    vf
    cv
    #
    cfv
    #
    cQ
    wceq
    #
    vf
    cT
    crio
    cG
    @3
    @6
    vf
    cT
    cG
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cP
    cQ
    cT
    cU
    cE
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    cdlemg1.b
    cdlemg1.l
    cdlemg1.j
    cdlemg1.m
    cdlemg1.a
    cdlemg1.h
    cdlemg1.u
    cdlemg1.d
    cdlemg1.e
    cdlemg1.g
    cdlemg1.t
    cdleme50ltrn
    #
    @3
    @4
    cT
    wcel
    #
    wa
    #
    @6
    @4
    cG
    wceq
    #
    @9
    @6
    @10
    @9
    @6
    wa
    #
    @0
    @8
    cG
    cT
    wcel
    #
    @1
    @5
    cP
    cG
    cfv
    #
    wceq
    @10
    @0
    @1
    @2
    @8
    @6
    simpll1
    @3
    @8
    @6
    simplr
    @3
    @12
    @8
    @6
    @7
    ad2antrr
    @0
    @1
    @2
    @8
    @6
    simpll2
    @11
    @5
    cQ
    @13
    @9
    @6
    simpr
    @3
    @13
    cQ
    wceq
    #
    @8
    @6
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cP
    cQ
    cU
    cE
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vs
    cdlemg1.b
    cdlemg1.l
    cdlemg1.j
    cdlemg1.m
    cdlemg1.a
    cdlemg1.h
    cdlemg1.u
    cdlemg1.d
    cdlemg1.e
    cdlemg1.g
    cdleme17d
    #
    ad2antrr
    eqtr4d
    cA
    cP
    cT
    @4
    cG
    cH
    cK
    c.le
    cW
    cdlemg1.l
    cdlemg1.a
    cdlemg1.h
    cdlemg1.t
    cdlemd
    syl311anc
    ex
    @9
    @6
    @10
    @14
    @3
    @14
    @8
    @15
    adantr
    @10
    @5
    @13
    cQ
    cP
    @4
    cG
    fveq1
    eqeq1d
    syl5ibrcom
    impbid
    riota5
    eqcomd
end
