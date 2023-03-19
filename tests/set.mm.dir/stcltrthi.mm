include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "wss.mm"
include "cch.mm"
include "wral.mm"
include "cst.mm"
include "wrex.mm"
include "cort.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "biid.mm"
include "stcltrlem2.mm"
include "rexlimiva.mm"
include "ax-mp.mm"

theorem stcltrthi
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vs: setvar s
  assume stcltrth.1: |- A e. CH
  assume stcltrth.2: |- B e. CH
  assume stcltrth.3: |- E. s e. States A. x e. CH A. y e. CH ( ( ( s ` x ) = 1 -> ( s ` y ) = 1 ) -> x C_ y )

  disjoint x y
  disjoint s x
  disjoint A x
  disjoint s y
  disjoint A y
  disjoint A s
  disjoint B x
  disjoint B y
  disjoint B s
  assert |- B C_ ( ( _|_ ` A ) vH ( A i^i B ) )

  proof
    vx
    cv
    #
    vs
    cv
    #
    cfv
    c1
    wceq
    vy
    cv
    #
    @1
    cfv
    c1
    wceq
    wi
    @0
    @2
    wss
    wi
    vy
    cch
    wral
    vx
    cch
    wral
    #
    vs
    cst
    wrex
    cB
    cA
    cort
    cfv
    cA
    cB
    cin
    chj
    co
    wss
    #
    stcltrth.3
    @3
    @4
    vs
    cst
    @1
    cst
    wcel
    @3
    wa
    #
    vx
    vy
    cA
    cB
    @1
    @5
    biid
    stcltrth.1
    stcltrth.2
    stcltrlem2
    rexlimiva
    ax-mp
end
