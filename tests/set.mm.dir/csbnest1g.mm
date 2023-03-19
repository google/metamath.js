include "wcel.mm"
include "cv.mm"
include "csb.mm"
include "wnfc.mm"
include "wal.mm"
include "wceq.mm"
include "nfcsb1v.mm"
include "ax-gen.mm"
include "csbnestgf.mm"
include "mpan2.mm"
include "csbco.mm"
include "csbeq2i.mm"
include "3eqtr3g.mm"

theorem csbnest1g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> [_ A / x ]_ [_ B / x ]_ C = [_ [_ A / x ]_ B / x ]_ C )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vy
    cB
    vx
    vy
    cv
    #
    cC
    csb
    #
    csb
    #
    csb
    #
    vy
    vx
    cA
    cB
    csb
    #
    @2
    csb
    #
    vx
    cA
    vx
    cB
    cC
    csb
    #
    csb
    vx
    @5
    cC
    csb
    @0
    vx
    @2
    wnfc
    #
    vy
    wal
    @4
    @6
    wceq
    @8
    vy
    vx
    @1
    cC
    nfcsb1v
    ax-gen
    vx
    vy
    cA
    cB
    @2
    cV
    csbnestgf
    mpan2
    vx
    cA
    @3
    @7
    vx
    vy
    cB
    cC
    csbco
    csbeq2i
    vx
    vy
    @5
    cC
    csbco
    3eqtr3g
end
