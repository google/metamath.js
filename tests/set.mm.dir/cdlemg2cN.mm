include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "crio.mm"
include "cdlemg1cN.mm"
include "eqid.mm"
include "cdlemg1b2.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "bitrd.mm"

theorem cdlemg2cN
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
  let vf: setvar f
  let cX: class X
  assume cdlemg2.b: |- B = ( Base ` K )
  assume cdlemg2.l: |- .<_ = ( le ` K )
  assume cdlemg2.j: |- .\/ = ( join ` K )
  assume cdlemg2.m: |- ./\ = ( meet ` K )
  assume cdlemg2.a: |- A = ( Atoms ` K )
  assume cdlemg2.h: |- H = ( LHyp ` K )
  assume cdlemg2.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg2.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemg2.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemg2.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemg2.g: |- G = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )

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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F ` P ) = Q ) -> ( F e. T <-> F = G ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
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
    w3a
    #
    cP
    cF
    cfv
    cQ
    wceq
    #
    wa
    #
    cF
    cT
    wcel
    cF
    cP
    vf
    cv
    cfv
    cQ
    wceq
    vf
    cT
    crio
    #
    wceq
    cF
    cG
    wceq
    cA
    cP
    cQ
    cT
    vf
    cF
    cH
    cK
    c.le
    cW
    cdlemg2.l
    cdlemg2.a
    cdlemg2.h
    cdlemg2.t
    cdlemg1cN
    @2
    @3
    cG
    cF
    @0
    @3
    cG
    wceq
    @1
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
    vf
    cE
    @3
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
    cdlemg2.u
    cdlemg2.d
    cdlemg2.e
    cdlemg2.g
    cdlemg2.t
    @3
    eqid
    cdlemg1b2
    adantr
    eqeq2d
    bitrd
end
