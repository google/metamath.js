include "wcel.mm"
include "co.mm"
include "cv.mm"
include "csb.mm"
include "wnfc.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "a1i.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "csbiegf.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem cdleme31se2
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cE: class E
  let c.or: class .\/
  let c.an: class ./\
  let cW: class W
  let cY: class Y
  assume cdleme31se2.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( R .\/ t ) ./\ W ) ) )
  assume cdleme31se2.y: |- Y = ( ( P .\/ Q ) ./\ ( [_ S / t ]_ D .\/ ( ( R .\/ S ) ./\ W ) ) )

  disjoint A t
  disjoint .\/ t
  disjoint ./\ t
  disjoint P t
  disjoint Q t
  disjoint R t
  disjoint S t
  disjoint W t
  assert |- ( S e. A -> [_ S / t ]_ E = Y )

  proof
    cS
    cA
    wcel
    #
    vt
    cS
    cP
    cQ
    c.or
    co
    #
    cD
    cR
    vt
    cv
    #
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
    vt
    cS
    cD
    csb
    #
    cR
    cS
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
    vt
    cS
    cE
    csb
    cY
    vt
    cS
    @6
    @11
    cA
    vt
    @11
    wnfc
    @0
    vt
    @1
    @10
    c.an
    vt
    @1
    nfcv
    vt
    c.an
    nfcv
    vt
    @7
    @9
    c.or
    vt
    cS
    cD
    nfcsb1v
    vt
    c.or
    nfcv
    vt
    @9
    nfcv
    nfov
    nfov
    a1i
    @2
    cS
    wceq
    #
    @5
    @10
    @1
    c.an
    @12
    cD
    @7
    @4
    @9
    c.or
    vt
    cS
    cD
    csbeq1a
    @12
    @3
    @8
    cW
    c.an
    @2
    cS
    cR
    c.or
    oveq2
    oveq1d
    oveq12d
    oveq2d
    csbiegf
    vt
    cS
    cE
    @6
    cdleme31se2.e
    csbeq2i
    cdleme31se2.y
    3eqtr4g
end
