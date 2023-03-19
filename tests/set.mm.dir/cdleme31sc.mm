include "wcel.mm"
include "cv.mm"
include "co.mm"
include "csb.mm"
include "nfcvd.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "csbiegf.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem cdleme31sc
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let c.or: class .\/
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vs: setvar s
  assume cdleme31sc.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme31sc.x: |- X = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )

  disjoint A s
  disjoint .\/ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint U s
  disjoint W s
  assert |- ( R e. A -> [_ R / s ]_ C = X )

  proof
    cR
    cA
    wcel
    #
    vs
    cR
    vs
    cv
    #
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
    #
    csb
    cR
    cU
    c.or
    co
    #
    cQ
    cP
    cR
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
    vs
    cR
    cC
    csb
    cX
    vs
    cR
    @6
    @11
    cA
    @0
    vs
    @11
    nfcvd
    @1
    cR
    wceq
    #
    @2
    @7
    @5
    @10
    c.an
    @1
    cR
    cU
    c.or
    oveq1
    @12
    @4
    @9
    cQ
    c.or
    @12
    @3
    @8
    cW
    c.an
    @1
    cR
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    csbiegf
    vs
    cR
    cC
    @6
    cdleme31sc.c
    csbeq2i
    cdleme31sc.x
    3eqtr4g
end
