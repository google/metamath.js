include "cref.mm"
include "wbr.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wi.mm"
include "cvv.mm"
include "refrel.mm"
include "brrelexi.mm"
include "cuni.mm"
include "wceq.mm"
include "eqid.mm"
include "isref.mm"
include "simplbda.mm"
include "mpancom.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "rspccv.mm"
include "syl.mm"
include "imp.mm"

theorem refssex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cS: class S
  let vy: setvar y

  disjoint B x
  disjoint S x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint S y
  assert |- ( ( A Ref B /\ S e. A ) -> E. x e. B S C_ x )

  proof
    cA
    cB
    cref
    wbr
    #
    cS
    cA
    wcel
    #
    cS
    vx
    cv
    #
    wss
    #
    vx
    cB
    wrex
    #
    @0
    vy
    cv
    #
    @2
    wss
    #
    vx
    cB
    wrex
    #
    vy
    cA
    wral
    #
    @1
    @4
    wi
    cA
    cvv
    wcel
    #
    @0
    @8
    cA
    cB
    cref
    refrel
    brrelexi
    @9
    @0
    cB
    cuni
    #
    cA
    cuni
    #
    wceq
    @8
    vy
    vx
    cA
    cB
    cvv
    @11
    @10
    @11
    eqid
    @10
    eqid
    isref
    simplbda
    mpancom
    @7
    @4
    vy
    cS
    cA
    @5
    cS
    wceq
    @6
    @3
    vx
    cB
    @5
    cS
    @2
    sseq1
    rexbidv
    rspccv
    syl
    imp
end
