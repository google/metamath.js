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
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "wreu.mm"
include "cdleme25c.mm"
include "riotacl.mm"
include "syl.mm"
include "syl5eqel.mm"

theorem cdleme25cl
  let vu: setvar u
  let cA: class A
  let cB: class B
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
  assume cdleme25cl.i: |- I = ( iota_ u e. B A. s e. A ( ( -. s .<_ W /\ -. s .<_ ( P .\/ Q ) ) -> u = N ) )

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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) ) ) -> I e. B )

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
    #
    cI
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    @2
    @0
    c.le
    wbr
    wn
    wa
    vu
    cv
    cN
    wceq
    wi
    vs
    cA
    wral
    #
    vu
    cB
    crio
    #
    cB
    cdleme25cl.i
    @1
    @3
    vu
    cB
    wreu
    @4
    cB
    wcel
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
    @3
    vu
    cB
    riotacl
    syl
    syl5eqel
end
