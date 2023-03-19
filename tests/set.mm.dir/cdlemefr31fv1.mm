include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "csb.mm"
include "cdlemefr32fva1.mm"
include "wceq.mm"
include "simp2rl.mm"
include "simp3.mm"
include "cdleme31sn2.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem cdlemefr31fv1
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let vs: setvar s
  assume cdlemefr27.b: |- B = ( Base ` K )
  assume cdlemefr27.l: |- .<_ = ( le ` K )
  assume cdlemefr27.j: |- .\/ = ( join ` K )
  assume cdlemefr27.m: |- ./\ = ( meet ` K )
  assume cdlemefr27.a: |- A = ( Atoms ` K )
  assume cdlemefr27.h: |- H = ( LHyp ` K )
  assume cdlemefr27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemefr27.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdlemefr27.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme29fr.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme29fr.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )
  assume cdleme43frv.x: |- X = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint U s
  disjoint W s
  disjoint s z
  disjoint H s
  disjoint K s
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint s x
  disjoint B s
  disjoint B x
  disjoint B z
  disjoint H z
  disjoint .\/ x
  disjoint .\/ z
  disjoint K z
  disjoint .<_ x
  disjoint .<_ z
  disjoint ./\ x
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R x
  disjoint R z
  disjoint W x
  disjoint W z
  disjoint P x
  disjoint Q x
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( F ` R ) = X )

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
    cQ
    wne
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    wa
    #
    cR
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    cR
    cF
    cfv
    vs
    cR
    cN
    csb
    #
    cX
    vx
    vz
    cA
    cB
    cC
    cP
    cQ
    cR
    cU
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    vs
    cdlemefr27.b
    cdlemefr27.l
    cdlemefr27.j
    cdlemefr27.m
    cdlemefr27.a
    cdlemefr27.h
    cdlemefr27.u
    cdlemefr27.c
    cdlemefr27.n
    cdleme29fr.o
    cdleme29fr.f
    cdlemefr32fva1
    @6
    @2
    @5
    @7
    cX
    wceq
    @2
    @3
    @1
    @0
    @5
    simp2rl
    @0
    @4
    @5
    simp3
    cA
    cX
    cC
    cP
    cQ
    cR
    cU
    cI
    c.or
    c.le
    c.an
    cN
    cW
    vs
    cdlemefr27.c
    cdlemefr27.n
    cdleme43frv.x
    cdleme31sn2
    syl2anc
    eqtrd
end
