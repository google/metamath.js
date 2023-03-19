include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "csb.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "eqid.mm"
include "cdlemefs32sn1aw.mm"
include "simpld.mm"
include "atbase.mm"
include "syl.mm"

theorem cdlemefs32snb
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  let cY: class Y
  assume cdlemefs32.b: |- B = ( Base ` K )
  assume cdlemefs32.l: |- .<_ = ( le ` K )
  assume cdlemefs32.j: |- .\/ = ( join ` K )
  assume cdlemefs32.m: |- ./\ = ( meet ` K )
  assume cdlemefs32.a: |- A = ( Atoms ` K )
  assume cdlemefs32.h: |- H = ( LHyp ` K )
  assume cdlemefs32.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemefs32.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs32.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemefs32.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) )
  assume cdlemefs32.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )

  disjoint s t
  disjoint s y
  disjoint A s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint D y
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint H y
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ y
  disjoint K s
  disjoint K t
  disjoint K y
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ y
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ y
  disjoint P s
  disjoint P t
  disjoint P y
  disjoint Q s
  disjoint Q t
  disjoint Q y
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint U t
  disjoint U y
  disjoint W s
  disjoint W t
  disjoint W y
  disjoint D s
  disjoint s x
  disjoint s z
  disjoint t x
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint .\/ x
  disjoint .\/ z
  disjoint .<_ x
  disjoint .<_ z
  disjoint ./\ x
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint W x
  disjoint W z
  disjoint Y y
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ R .<_ ( P .\/ Q ) ) -> [_ R / s ]_ N e. B )

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
    cP
    cQ
    wne
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    wa
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    w3a
    #
    vs
    cR
    cN
    csb
    #
    cA
    wcel
    #
    @2
    cB
    wcel
    @1
    @3
    @2
    cW
    c.le
    wbr
    wn
    vy
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cU
    cE
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
    @0
    cD
    cR
    vt
    cv
    #
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
    @4
    cW
    c.le
    wbr
    wn
    @4
    @0
    c.le
    wbr
    wn
    wa
    vy
    cv
    @5
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    #
    vs
    cdlemefs32.b
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.m
    cdlemefs32.a
    cdlemefs32.h
    cdlemefs32.u
    cdlemefs32.d
    cdlemefs32.e
    cdlemefs32.i
    cdlemefs32.n
    @5
    eqid
    @6
    eqid
    cdlemefs32sn1aw
    simpld
    cA
    cB
    @2
    cK
    cdlemefs32.b
    cdlemefs32.a
    atbase
    syl
end
