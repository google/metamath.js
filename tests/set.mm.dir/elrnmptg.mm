include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "wral.mm"
include "rnmpt.mm"
include "eleq2i.mm"
include "cvv.mm"
include "wi.mm"
include "wb.mm"
include "wa.mm"
include "r19.29.mm"
include "eleq1.mm"
include "biimparc.mm"
include "elexd.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab3g.mm"
include "syl5bb.mm"

theorem elrnmptg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  assume rnmpt.1: |- F = ( x e. A |-> B )

  disjoint C x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint x y
  disjoint x z
  disjoint C y
  disjoint C z
  assert |- ( A. x e. A B e. V -> ( C e. ran F <-> E. x e. A C = B ) )

  proof
    cC
    cF
    crn
    #
    wcel
    cC
    vy
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    wcel
    #
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    #
    cC
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @0
    @4
    cC
    vx
    vy
    cA
    cB
    cF
    rnmpt.1
    rnmpt
    eleq2i
    @7
    @9
    cC
    cvv
    wcel
    #
    wi
    @5
    @9
    wb
    @7
    @9
    @10
    @7
    @9
    wa
    @6
    @8
    wa
    #
    vx
    cA
    wrex
    @10
    @6
    @8
    vx
    cA
    r19.29
    @11
    @10
    vx
    cA
    @11
    cC
    cV
    @8
    cC
    cV
    wcel
    @6
    cC
    cB
    cV
    eleq1
    biimparc
    elexd
    rexlimivw
    syl
    ex
    @3
    @9
    vy
    cC
    cvv
    @1
    cC
    wceq
    @2
    @8
    vx
    cA
    @1
    cC
    cB
    eqeq1
    rexbidv
    elab3g
    syl
    syl5bb
end
