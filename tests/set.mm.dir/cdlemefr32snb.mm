include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "csb.mm"
include "cdlemefr32sn2aw.mm"
include "simpld.mm"
include "atbase.mm"
include "syl.mm"

theorem cdlemefr32snb
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
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

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint U s
  disjoint W s
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> [_ R / s ]_ N e. B )

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
    c.le
    wbr
    wn
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
    @1
    cB
    wcel
    @0
    @2
    @1
    cW
    c.le
    wbr
    wn
    cA
    cB
    cC
    cP
    cQ
    cR
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
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
    cdlemefr32sn2aw
    simpld
    cA
    cB
    @1
    cK
    cdlemefr27.b
    cdlemefr27.a
    atbase
    syl
end
