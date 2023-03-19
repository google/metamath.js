include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wne.mm"
include "cif.mm"
include "simpr2.mm"
include "iftrued.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr1.mm"
include "simpr3.mm"
include "cdleme25cl.mm"
include "syl312anc.mm"
include "eqeltrd.mm"
include "syl5eqel.mm"

theorem cdlemefs27cl
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
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
  assume cdlemefs26.b: |- B = ( Base ` K )
  assume cdlemefs26.l: |- .<_ = ( le ` K )
  assume cdlemefs26.j: |- .\/ = ( join ` K )
  assume cdlemefs26.m: |- ./\ = ( meet ` K )
  assume cdlemefs26.a: |- A = ( Atoms ` K )
  assume cdlemefs26.h: |- H = ( LHyp ` K )
  assume cdlemefs27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemefs27.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs27.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemefs27.i: |- I = ( iota_ u e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> u = E ) )
  assume cdlemefs27.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )

  disjoint t u
  disjoint A t
  disjoint A u
  disjoint B t
  disjoint B u
  disjoint E u
  disjoint H t
  disjoint .\/ t
  disjoint .\/ u
  disjoint K t
  disjoint .<_ t
  disjoint .<_ u
  disjoint ./\ t
  disjoint ./\ u
  disjoint P t
  disjoint P u
  disjoint Q t
  disjoint Q u
  disjoint U t
  disjoint U u
  disjoint W t
  disjoint W u
  disjoint s t
  disjoint s u
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( s e. A /\ -. s .<_ W ) /\ s .<_ ( P .\/ Q ) /\ P =/= Q ) ) -> N e. B )

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
    vs
    cv
    #
    cA
    wcel
    @4
    cW
    c.le
    wbr
    wn
    wa
    #
    @4
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    cP
    cQ
    wne
    #
    w3a
    #
    wa
    #
    cN
    @6
    cI
    cC
    cif
    #
    cB
    cdlemefs27.n
    @9
    @10
    cI
    cB
    @9
    @6
    cI
    cC
    @3
    @5
    @6
    @7
    simpr2
    #
    iftrued
    @9
    @0
    @1
    @2
    @5
    @7
    @6
    cI
    cB
    wcel
    @0
    @1
    @2
    @8
    simpl1
    @0
    @1
    @2
    @8
    simpl2
    @0
    @1
    @2
    @8
    simpl3
    @3
    @5
    @6
    @7
    simpr1
    @3
    @5
    @6
    @7
    simpr3
    @11
    vu
    cA
    cB
    cP
    cQ
    @4
    cU
    cD
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cE
    cW
    vt
    cdlemefs26.b
    cdlemefs26.l
    cdlemefs26.j
    cdlemefs26.m
    cdlemefs26.a
    cdlemefs26.h
    cdlemefs27.u
    cdlemefs27.d
    cdlemefs27.e
    cdlemefs27.i
    cdleme25cl
    syl312anc
    eqeltrd
    syl5eqel
end
