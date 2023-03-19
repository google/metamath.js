include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "csb.mm"
include "nfeq2.mm"
include "nfcsb1v.mm"
include "nfeq.mm"
include "nfim.mm"
include "eqeq1.mm"
include "csbeq1a.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "chvar.mm"

theorem csbhypf
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume csbhypf.1: |- F/_ x A
  assume csbhypf.2: |- F/_ x C
  assume csbhypf.3: |- ( x = A -> B = C )

  disjoint x y
  assert |- ( y = A -> [_ y / x ]_ B = C )

  proof
    vx
    cv
    #
    cA
    wceq
    #
    cB
    cC
    wceq
    #
    wi
    vy
    cv
    #
    cA
    wceq
    #
    vx
    @3
    cB
    csb
    #
    cC
    wceq
    #
    wi
    vx
    vy
    @4
    @6
    vx
    vx
    @3
    cA
    csbhypf.1
    nfeq2
    vx
    @5
    cC
    vx
    @3
    cB
    nfcsb1v
    csbhypf.2
    nfeq
    nfim
    @0
    @3
    wceq
    #
    @1
    @4
    @2
    @6
    @0
    @3
    cA
    eqeq1
    @7
    cB
    @5
    cC
    vx
    @3
    cB
    csbeq1a
    eqeq1d
    imbi12d
    csbhypf.3
    chvar
end
