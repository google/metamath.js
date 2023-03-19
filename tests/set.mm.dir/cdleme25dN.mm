include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wreu.mm"
include "wi.mm"
include "wral.mm"
include "cdleme25c.mm"
include "wb.mm"
include "simp11l.mm"
include "adantr.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simpl2l.mm"
include "simpr.mm"
include "cdleme22gb.mm"
include "syl222anc.mm"
include "ex.mm"
include "a1dd.mm"
include "ralrimiv.mm"
include "simp12.mm"
include "simp13.mm"
include "simp3l.mm"
include "cdlemb2.mm"
include "syl221anc.mm"
include "reusv2.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem cdleme25dN
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  assume cdleme24.b: |- B = ( Base ` K )
  assume cdleme24.l: |- .<_ = ( le ` K )
  assume cdleme24.j: |- .\/ = ( join ` K )
  assume cdleme24.m: |- ./\ = ( meet ` K )
  assume cdleme24.a: |- A = ( Atoms ` K )
  assume cdleme24.h: |- H = ( LHyp ` K )
  assume cdleme24.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme24.f: |- F = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme24.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ s ) ./\ W ) ) )

  disjoint N u
  disjoint s u
  disjoint U s
  disjoint U u
  disjoint s u
  disjoint A s
  disjoint A u
  disjoint B s
  disjoint B u
  disjoint H s
  disjoint .\/ s
  disjoint .\/ u
  disjoint K s
  disjoint .<_ s
  disjoint .<_ u
  disjoint ./\ s
  disjoint ./\ u
  disjoint P s
  disjoint P u
  disjoint Q s
  disjoint Q u
  disjoint R s
  disjoint R u
  disjoint W s
  disjoint W u
  disjoint t u
  disjoint N t
  disjoint s t
  disjoint t u
  disjoint A t
  disjoint B t
  disjoint H t
  disjoint .\/ t
  disjoint K t
  disjoint .<_ t
  disjoint P t
  disjoint Q t
  disjoint R t
  disjoint W t
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) ) ) -> E! u e. B E. s e. A ( ( -. s .<_ W /\ -. s .<_ ( P .\/ Q ) ) /\ u = N ) )

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
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
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
    #
    cP
    cQ
    wne
    #
    cR
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
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    @18
    @14
    c.le
    wbr
    wn
    wa
    #
    vu
    cv
    cN
    wceq
    #
    wa
    vs
    cA
    wrex
    vu
    cB
    wreu
    #
    @19
    @20
    wi
    vs
    cA
    wral
    vu
    cB
    wreu
    #
    vu
    cA
    cB
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    vs
    cdleme24.b
    cdleme24.l
    cdleme24.j
    cdleme24.m
    cdleme24.a
    cdleme24.h
    cdleme24.u
    cdleme24.f
    cdleme24.n
    cdleme25c
    @17
    @19
    cN
    cB
    wcel
    #
    wi
    #
    vs
    cA
    wral
    @19
    vs
    cA
    wrex
    #
    @21
    @22
    wb
    @17
    @24
    vs
    cA
    @17
    @18
    cA
    wcel
    #
    @23
    @19
    @17
    @26
    @23
    @17
    @26
    wa
    @0
    @1
    @3
    @6
    @10
    @26
    @23
    @17
    @0
    @26
    @0
    @1
    @5
    @8
    @12
    @16
    simp11l
    #
    adantr
    @17
    @1
    @26
    @0
    @1
    @5
    @8
    @12
    @16
    simp11r
    #
    adantr
    @17
    @3
    @26
    @3
    @4
    @2
    @8
    @12
    @16
    simp12l
    adantr
    @17
    @6
    @26
    @6
    @7
    @2
    @5
    @12
    @16
    simp13l
    adantr
    @10
    @11
    @9
    @16
    @26
    simpl2l
    @17
    @26
    simpr
    cA
    cB
    cP
    cQ
    cR
    @18
    cU
    cF
    cN
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme24.l
    cdleme24.j
    cdleme24.m
    cdleme24.a
    cdleme24.h
    cdleme24.u
    cdleme24.f
    cdleme24.n
    cdleme24.b
    cdleme22gb
    syl222anc
    ex
    a1dd
    ralrimiv
    @17
    @0
    @1
    @5
    @8
    @13
    @25
    @27
    @28
    @2
    @5
    @8
    @12
    @16
    simp12
    @2
    @5
    @8
    @12
    @16
    simp13
    @9
    @12
    @13
    @15
    simp3l
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vs
    cdleme24.l
    cdleme24.j
    cdleme24.a
    cdleme24.h
    cdlemb2
    syl221anc
    @19
    vu
    vs
    cB
    cA
    cN
    reusv2
    syl2anc
    mpbird
end
