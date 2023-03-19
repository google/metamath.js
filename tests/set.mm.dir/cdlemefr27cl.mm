include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "cif.mm"
include "simpr2.mm"
include "iffalsed.mm"
include "syl5eq.mm"
include "simpl1l.mm"
include "simpl1r.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simpr1.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "eqeltrd.mm"

theorem cdlemefr27cl
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ P e. A /\ Q e. A ) /\ ( s e. A /\ -. s .<_ ( P .\/ Q ) /\ P =/= Q ) ) -> N e. B )

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
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    vs
    cv
    #
    cA
    wcel
    #
    @6
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    wn
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
    cC
    cB
    @12
    cN
    @8
    cI
    cC
    cif
    cC
    cdlemefr27.n
    @12
    @8
    cI
    cC
    @5
    @7
    @9
    @10
    simpr2
    iffalsed
    syl5eq
    @12
    @0
    @1
    @3
    @4
    @7
    cC
    cB
    wcel
    @0
    @1
    @3
    @4
    @11
    simpl1l
    @0
    @1
    @3
    @4
    @11
    simpl1r
    @2
    @3
    @4
    @11
    simpl2
    @2
    @3
    @4
    @11
    simpl3
    @5
    @7
    @9
    @10
    simpr1
    cA
    cB
    cP
    cQ
    @6
    cU
    cC
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemefr27.l
    cdlemefr27.j
    cdlemefr27.m
    cdlemefr27.a
    cdlemefr27.h
    cdlemefr27.u
    cdlemefr27.c
    cdlemefr27.b
    cdleme1b
    syl23anc
    eqeltrd
end
