include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wn.mm"
include "w3a.mm"
include "wceq.mm"
include "simp11.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp12l.mm"
include "simp12r.mm"
include "cdleme25cl.mm"
include "syl322anc.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp31.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "riotasv.mm"
include "syl112anc.mm"
include "simp23.mm"
include "simp33.mm"
include "simp32.mm"
include "cdleme22f.mm"
include "syl331anc.mm"
include "eqbrtrd.mm"

theorem cdleme26f
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  assume cdleme26.b: |- B = ( Base ` K )
  assume cdleme26.l: |- .<_ = ( le ` K )
  assume cdleme26.j: |- .\/ = ( join ` K )
  assume cdleme26.m: |- ./\ = ( meet ` K )
  assume cdleme26.a: |- A = ( Atoms ` K )
  assume cdleme26.h: |- H = ( LHyp ` K )
  assume cdleme26f.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme26f.f: |- F = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme26f.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( S .\/ t ) ./\ W ) ) )
  assume cdleme26f.i: |- I = ( iota_ u e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> u = N ) )

  disjoint t u
  disjoint A t
  disjoint A u
  disjoint B t
  disjoint B u
  disjoint H t
  disjoint .\/ t
  disjoint .\/ u
  disjoint K t
  disjoint .<_ t
  disjoint .<_ u
  disjoint ./\ t
  disjoint ./\ u
  disjoint N u
  disjoint P t
  disjoint P u
  disjoint Q t
  disjoint Q u
  disjoint S t
  disjoint S u
  disjoint U t
  disjoint U u
  disjoint W t
  disjoint W u
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P =/= Q /\ S .<_ ( P .\/ Q ) ) /\ ( t e. A /\ -. t .<_ W ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( -. t .<_ ( P .\/ Q ) /\ ( S =/= t /\ S .<_ ( t .\/ V ) ) /\ ( V e. A /\ V .<_ W ) ) ) -> I .<_ ( F .\/ V ) )

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
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    vt
    cv
    #
    cA
    wcel
    #
    @5
    cW
    c.le
    wbr
    wn
    #
    wa
    #
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
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    @5
    @2
    c.le
    wbr
    wn
    #
    cS
    @5
    wne
    cS
    @5
    cV
    c.or
    co
    c.le
    wbr
    wa
    #
    cV
    cA
    wcel
    cV
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    w3a
    #
    cI
    cN
    cF
    cV
    c.or
    co
    #
    c.le
    @20
    cI
    cB
    wcel
    #
    @6
    @7
    @16
    cI
    cN
    wceq
    @20
    @0
    @10
    @11
    @12
    @13
    @1
    @3
    @22
    @0
    @4
    @8
    @15
    @19
    simp11
    #
    @9
    @10
    @11
    @14
    @19
    simp21
    #
    @9
    @10
    @11
    @14
    @19
    simp22
    #
    @12
    @13
    @10
    @11
    @9
    @19
    simp23l
    @12
    @13
    @10
    @11
    @9
    @19
    simp23r
    @1
    @3
    @0
    @8
    @15
    @19
    simp12l
    @1
    @3
    @0
    @8
    @15
    @19
    simp12r
    vu
    cA
    cB
    cP
    cQ
    cS
    cU
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
    vt
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26f.u
    cdleme26f.f
    cdleme26f.n
    cdleme26f.i
    cdleme25cl
    syl322anc
    @6
    @7
    @0
    @4
    @15
    @19
    simp13l
    #
    @6
    @7
    @0
    @4
    @15
    @19
    simp13r
    @9
    @15
    @16
    @17
    @18
    simp31
    @7
    @16
    wa
    vu
    vt
    cB
    cA
    cN
    cI
    cB
    cK
    cbs
    cfv
    cvv
    cdleme26.b
    cK
    cbs
    fvex
    eqeltri
    cdleme26f.i
    riotasv
    syl112anc
    @20
    @0
    @10
    @11
    @14
    @6
    @18
    @17
    cN
    @21
    c.le
    wbr
    @23
    @24
    @25
    @9
    @10
    @11
    @14
    @19
    simp23
    @26
    @9
    @15
    @16
    @17
    @18
    simp33
    @9
    @15
    @16
    @17
    @18
    simp32
    cA
    cP
    cQ
    cS
    @5
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cV
    cW
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26f.u
    cdleme26f.f
    cdleme26f.n
    cdleme22f
    syl331anc
    eqbrtrd
end
