include "wcel.mm"
include "csb.mm"
include "co.mm"
include "cv.mm"
include "csbeq2i.mm"
include "nfcvd.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "3eqtr4g.mm"
include "csbiegf.mm"
include "syl5eq.mm"
include "csbeq2dv.mm"
include "eqid.mm"
include "cdleme31se.mm"
include "sylan9eqr.mm"

theorem cdleme31sde
  let vt: setvar t
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let c.or: class .\/
  let c.an: class ./\
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  assume cdleme31sde.c: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme31sde.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme31sde.x: |- Y = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme31sde.z: |- Z = ( ( P .\/ Q ) ./\ ( Y .\/ ( ( R .\/ S ) ./\ W ) ) )

  disjoint s t
  disjoint A s
  disjoint A t
  disjoint .\/ s
  disjoint .\/ t
  disjoint ./\ s
  disjoint ./\ t
  disjoint P s
  disjoint P t
  disjoint Q s
  disjoint Q t
  disjoint R s
  disjoint S s
  disjoint S t
  disjoint W s
  disjoint W t
  disjoint Y s
  disjoint Y t
  assert |- ( ( R e. A /\ S e. A ) -> [_ R / s ]_ [_ S / t ]_ E = Z )

  proof
    cS
    cA
    wcel
    #
    cR
    cA
    wcel
    vs
    cR
    vt
    cS
    cE
    csb
    #
    csb
    vs
    cR
    cP
    cQ
    c.or
    co
    #
    cY
    vs
    cv
    #
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
    csb
    cZ
    @0
    vs
    cR
    @1
    @7
    @0
    @1
    vt
    cS
    @2
    cD
    @3
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
    @7
    vt
    cS
    cE
    @12
    cdleme31sde.e
    csbeq2i
    vt
    cS
    @12
    @7
    cA
    @0
    vt
    @7
    nfcvd
    @8
    cS
    wceq
    #
    @11
    @6
    @2
    c.an
    @13
    cD
    cY
    @10
    @5
    c.or
    @13
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
    cS
    cU
    c.or
    co
    #
    cQ
    cP
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
    cD
    cY
    @13
    @14
    @18
    @17
    @21
    c.an
    @8
    cS
    cU
    c.or
    oveq1
    @13
    @16
    @20
    cQ
    c.or
    @13
    @15
    @19
    cW
    c.an
    @8
    cS
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    cdleme31sde.c
    cdleme31sde.x
    3eqtr4g
    @13
    @9
    @4
    cW
    c.an
    @8
    cS
    @3
    c.or
    oveq2
    oveq1d
    oveq12d
    oveq2d
    csbiegf
    syl5eq
    csbeq2dv
    cA
    cY
    cP
    cQ
    cR
    cS
    @7
    c.or
    c.an
    cW
    cZ
    vs
    @7
    eqid
    cdleme31sde.z
    cdleme31se
    sylan9eqr
end
