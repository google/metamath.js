include "wcel.mm"
include "co.mm"
include "cv.mm"
include "csb.mm"
include "nfcvd.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "csbiegf.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem cdleme31se
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cE: class E
  let c.or: class .\/
  let c.an: class ./\
  let cW: class W
  let cY: class Y
  let vs: setvar s
  assume cdleme31se.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ T ) ./\ W ) ) )
  assume cdleme31se.y: |- Y = ( ( P .\/ Q ) ./\ ( D .\/ ( ( R .\/ T ) ./\ W ) ) )

  disjoint A s
  disjoint D s
  disjoint .\/ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint W s
  disjoint T s
  assert |- ( R e. A -> [_ R / s ]_ E = Y )

  proof
    cR
    cA
    wcel
    #
    vs
    cR
    cP
    cQ
    c.or
    co
    #
    cD
    vs
    cv
    #
    cT
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
    @1
    cD
    cR
    cT
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
    cE
    csb
    cY
    vs
    cR
    @6
    @10
    cA
    @0
    vs
    @10
    nfcvd
    @2
    cR
    wceq
    #
    @5
    @9
    @1
    c.an
    @11
    @4
    @8
    cD
    c.or
    @11
    @3
    @7
    cW
    c.an
    @2
    cR
    cT
    c.or
    oveq1
    oveq1d
    oveq2d
    oveq2d
    csbiegf
    vs
    cR
    cE
    @6
    cdleme31se.e
    csbeq2i
    cdleme31se.y
    3eqtr4g
end
