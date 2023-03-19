include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cdleme25a.mm"
include "eqid.mm"
include "cdleme24.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "reusv3.mm"
include "biimpd.mm"
include "sylc.mm"

theorem cdleme25b
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) ) ) -> E. u e. B A. s e. A ( ( -. s .<_ W /\ -. s .<_ ( P .\/ Q ) ) -> u = N ) )

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
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    cP
    cQ
    wne
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wa
    w3a
    vs
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @1
    @0
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cN
    cB
    wcel
    wa
    vs
    cA
    wrex
    #
    @6
    vt
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @8
    @0
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wa
    cN
    @0
    @8
    cU
    c.or
    co
    #
    cQ
    cP
    @8
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    cR
    @8
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    wi
    vt
    cA
    wral
    vs
    cA
    wral
    #
    @6
    vu
    cv
    cN
    wceq
    wi
    vs
    cA
    wral
    vu
    cB
    wrex
    #
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
    cdleme25a
    vt
    cA
    cB
    cP
    cQ
    cR
    cU
    cF
    @18
    cH
    c.or
    cK
    c.le
    c.an
    cN
    @22
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
    @18
    eqid
    @22
    eqid
    cdleme24
    @7
    @23
    @24
    @6
    @13
    vu
    vs
    vt
    cB
    cA
    cN
    @22
    @1
    @8
    wceq
    #
    @3
    @10
    @5
    @12
    @25
    @2
    @9
    @1
    @8
    cW
    c.le
    breq1
    notbid
    @25
    @4
    @11
    @1
    @8
    @0
    c.le
    breq1
    notbid
    anbi12d
    @25
    cN
    @0
    cF
    cR
    @1
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    @22
    cdleme24.n
    @25
    @28
    @21
    @0
    c.an
    @25
    cF
    @18
    @27
    @20
    c.or
    @25
    cF
    @1
    cU
    c.or
    co
    #
    cQ
    cP
    @1
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    @18
    cdleme24.f
    @25
    @29
    @14
    @32
    @17
    c.an
    @1
    @8
    cU
    c.or
    oveq1
    @25
    @31
    @16
    cQ
    c.or
    @25
    @30
    @15
    cW
    c.an
    @1
    @8
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    syl5eq
    @25
    @26
    @19
    cW
    c.an
    @1
    @8
    cR
    c.or
    oveq2
    oveq1d
    oveq12d
    oveq2d
    syl5eq
    reusv3
    biimpd
    sylc
end
