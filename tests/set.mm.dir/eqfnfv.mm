include "wfn.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wral.mm"
include "wb.mm"
include "dffn5.mm"
include "eqeq12.mm"
include "syl2anb.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "rgenw.mm"
include "mpteqb.mm"
include "ax-mp.mm"
include "syl6bb.mm"

theorem eqfnfv
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let wph: wff ph

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint ph x
  assert |- ( ( F Fn A /\ G Fn A ) -> ( F = G <-> A. x e. A ( F ` x ) = ( G ` x ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    wa
    cF
    cG
    wceq
    #
    vx
    cA
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    vx
    cA
    @3
    cG
    cfv
    #
    cmpt
    #
    wceq
    #
    @4
    @6
    wceq
    vx
    cA
    wral
    #
    @0
    cF
    @5
    wceq
    cG
    @7
    wceq
    @2
    @8
    wb
    @1
    vx
    cA
    cF
    dffn5
    vx
    cA
    cG
    dffn5
    cF
    @5
    cG
    @7
    eqeq12
    syl2anb
    @4
    cvv
    wcel
    #
    vx
    cA
    wral
    @8
    @9
    wb
    @10
    vx
    cA
    @3
    cF
    fvex
    rgenw
    vx
    cA
    @4
    @6
    cvv
    mpteqb
    ax-mp
    syl6bb
end
