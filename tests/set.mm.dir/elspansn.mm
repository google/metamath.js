include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "wb.mm"
include "c0v.mm"
include "cif.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "bibi12d.mm"
include "ifhvhv0.mm"
include "elspansni.mm"
include "dedth.mm"

theorem elspansn
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A e. ~H -> ( B e. ( span ` { A } ) <-> E. x e. CC B = ( x .h A ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    cA
    csn
    #
    cspn
    cfv
    #
    wcel
    #
    cB
    vx
    cv
    #
    cA
    csm
    co
    #
    wceq
    #
    vx
    cc
    wrex
    #
    wb
    cB
    @0
    cA
    c0v
    cif
    #
    csn
    #
    cspn
    cfv
    #
    wcel
    #
    cB
    @4
    @8
    csm
    co
    #
    wceq
    #
    vx
    cc
    wrex
    #
    wb
    cA
    c0v
    cA
    @8
    wceq
    #
    @3
    @11
    @7
    @14
    @15
    @2
    @10
    cB
    @15
    @1
    @9
    cspn
    cA
    @8
    sneq
    fveq2d
    eleq2d
    @15
    @6
    @13
    vx
    cc
    @15
    @5
    @12
    cB
    cA
    @8
    @4
    csm
    oveq2
    eqeq2d
    rexbidv
    bibi12d
    vx
    @8
    cB
    cA
    ifhvhv0
    elspansni
    dedth
end
