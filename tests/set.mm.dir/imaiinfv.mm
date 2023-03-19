include "wfn.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cres.mm"
include "cfv.mm"
include "ciin.mm"
include "crn.mm"
include "cint.mm"
include "cima.mm"
include "wceq.mm"
include "fnssres.mm"
include "fniinfv.mm"
include "syl.mm"
include "fvres.mm"
include "iineq2i.mm"
include "eqcomi.mm"
include "df-ima.mm"
include "inteqi.mm"
include "3eqtr4g.mm"

theorem imaiinfv
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F

  disjoint B x
  disjoint F x
  assert |- ( ( F Fn A /\ B C_ A ) -> |^|_ x e. B ( F ` x ) = |^| ( F " B ) )

  proof
    cF
    cA
    wfn
    cB
    cA
    wss
    wa
    #
    vx
    cB
    vx
    cv
    #
    cF
    cB
    cres
    #
    cfv
    #
    ciin
    #
    @2
    crn
    #
    cint
    #
    vx
    cB
    @1
    cF
    cfv
    #
    ciin
    #
    cF
    cB
    cima
    #
    cint
    @0
    @2
    cB
    wfn
    @4
    @6
    wceq
    cA
    cB
    cF
    fnssres
    vx
    cB
    @2
    fniinfv
    syl
    @4
    @8
    vx
    cB
    @3
    @7
    @1
    cB
    cF
    fvres
    iineq2i
    eqcomi
    @9
    @5
    cF
    cB
    df-ima
    inteqi
    3eqtr4g
end
