include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "crab.mm"
include "wral.mm"
include "wdisj.mm"
include "wcel.mm"
include "wi.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfeq1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "eqeq1d.mm"
include "elrabf.mm"
include "ax-1.mm"
include "simplbiim.mm"
include "impcom.mm"
include "rgen2.mm"
include "invdisj.mm"
include "ax-mp.mm"

theorem invdisjrab
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint B x
  disjoint C y
  disjoint x y
  disjoint A z
  disjoint B z
  disjoint x z
  disjoint C z
  disjoint y z
  assert |- Disj_ y e. A { x e. B | C = y }

  proof
    vx
    vz
    cv
    #
    cC
    csb
    #
    vy
    cv
    #
    wceq
    #
    vz
    cC
    @2
    wceq
    #
    vx
    cB
    crab
    #
    wral
    vy
    cA
    wral
    vy
    cA
    @5
    wdisj
    @3
    vy
    vz
    cA
    @5
    @0
    @5
    wcel
    #
    @2
    cA
    wcel
    #
    @3
    @6
    @0
    cB
    wcel
    @3
    @7
    @3
    wi
    @4
    @3
    vx
    @0
    cB
    vx
    @0
    nfcv
    vx
    cB
    nfcv
    vx
    @1
    @2
    vx
    @0
    cC
    nfcsb1v
    nfeq1
    vx
    vz
    weq
    cC
    @1
    @2
    vx
    @0
    cC
    csbeq1a
    eqeq1d
    elrabf
    @3
    @7
    ax-1
    simplbiim
    impcom
    rgen2
    vy
    vz
    cA
    @5
    @1
    invdisj
    ax-mp
end
