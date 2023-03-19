include "cxp.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "co.mm"
include "cmpt2.mm"
include "dffn5.mm"
include "cop.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "mpt2mpt.mm"
include "eqeq2i.mm"
include "bitri.mm"

theorem fnov
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vz: setvar z

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint B z
  disjoint F z
  assert |- ( F Fn ( A X. B ) <-> F = ( x e. A , y e. B |-> ( x F y ) ) )

  proof
    cF
    cA
    cB
    cxp
    #
    wfn
    cF
    vz
    @0
    vz
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    wceq
    cF
    vx
    vy
    cA
    cB
    vx
    cv
    #
    vy
    cv
    #
    cF
    co
    #
    cmpt2
    #
    wceq
    vz
    @0
    cF
    dffn5
    @3
    @7
    cF
    vx
    vy
    vz
    cA
    cB
    @2
    @6
    @1
    @4
    @5
    cop
    #
    wceq
    @2
    @8
    cF
    cfv
    @6
    @1
    @8
    cF
    fveq2
    @4
    @5
    cF
    df-ov
    syl6eqr
    mpt2mpt
    eqeq2i
    bitri
end
