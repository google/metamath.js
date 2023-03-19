include "wcel.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "w3a.mm"
include "wa.mm"
include "ciin.mm"
include "cmpt.mm"
include "crn.mm"
include "cint.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "simpr1.mm"
include "dfiin2g.mm"
include "syl.mm"
include "eqid.mm"
include "rnmpt.mm"
include "inteqi.mm"
include "syl6eqr.mm"
include "wf.mm"
include "fmpt.mm"
include "3anbi1i.mm"
include "intrnfi.mm"
include "sylan2b.mm"
include "eqeltrd.mm"

theorem iinfi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint C x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( C e. V /\ ( A. x e. A B e. C /\ A =/= (/) /\ A e. Fin ) ) -> |^|_ x e. A B e. ( fi ` C ) )

  proof
    cC
    cV
    wcel
    #
    cB
    cC
    wcel
    vx
    cA
    wral
    #
    cA
    c0
    wne
    #
    cA
    cfn
    wcel
    #
    w3a
    #
    wa
    #
    vx
    cA
    cB
    ciin
    #
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cint
    #
    cC
    cfi
    cfv
    #
    @5
    @6
    vy
    cv
    cB
    wceq
    vx
    cA
    wrex
    vy
    cab
    #
    cint
    #
    @9
    @5
    @1
    @6
    @12
    wceq
    @0
    @1
    @2
    @3
    simpr1
    vx
    vy
    cA
    cB
    cC
    dfiin2g
    syl
    @8
    @11
    vx
    vy
    cA
    cB
    @7
    @7
    eqid
    #
    rnmpt
    inteqi
    syl6eqr
    @4
    @0
    cA
    cC
    @7
    wf
    #
    @2
    @3
    w3a
    @9
    @10
    wcel
    @1
    @14
    @2
    @3
    vx
    cA
    cC
    cB
    @7
    @13
    fmpt
    3anbi1i
    cA
    cC
    @7
    cV
    intrnfi
    sylan2b
    eqeltrd
end
