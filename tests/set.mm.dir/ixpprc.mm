include "cixp.mm"
include "c0.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "wex.mm"
include "neq0.mm"
include "wfn.mm"
include "ixpfn.mm"
include "cdm.mm"
include "fndm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "syl.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "con1i.mm"

theorem ixpprc
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vf: setvar f

  disjoint A x
  disjoint f x
  disjoint A f
  disjoint B f
  assert |- ( -. A e. _V -> X_ x e. A B = (/) )

  proof
    vx
    cA
    cB
    cixp
    #
    c0
    wceq
    #
    cA
    cvv
    wcel
    #
    @1
    wn
    vf
    cv
    #
    @0
    wcel
    #
    vf
    wex
    @2
    vf
    @0
    neq0
    @4
    @2
    vf
    @4
    @3
    cA
    wfn
    #
    @2
    vx
    cA
    cB
    @3
    ixpfn
    @5
    cA
    @3
    cdm
    cvv
    cA
    @3
    fndm
    @3
    vf
    vex
    dmex
    syl6eqelr
    syl
    exlimiv
    sylbi
    con1i
end
