include "wsmo.mm"
include "cdm.mm"
include "con0.mm"
include "wf.mm"
include "word.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "feq2i.mm"
include "mpbir.mm"
include "wceq.mm"
include "wb.mm"
include "ordeq.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "syl2anb.mm"
include "rgen2a.mm"
include "df-smo.mm"
include "mpbir3an.mm"

theorem issmo
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume issmo.1: |- A : B --> On
  assume issmo.2: |- Ord B
  assume issmo.3: |- ( ( x e. B /\ y e. B ) -> ( x e. y -> ( A ` x ) e. ( A ` y ) ) )
  assume issmo.4: |- dom A = B

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- Smo A

  proof
    cA
    wsmo
    cA
    cdm
    #
    con0
    cA
    wf
    #
    @0
    word
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    @3
    cA
    cfv
    @4
    cA
    cfv
    wcel
    wi
    #
    vy
    @0
    wral
    vx
    @0
    wral
    @1
    cB
    con0
    cA
    wf
    issmo.1
    @0
    cB
    con0
    cA
    issmo.4
    feq2i
    mpbir
    @2
    cB
    word
    #
    issmo.2
    @0
    cB
    wceq
    @2
    @6
    wb
    issmo.4
    @0
    cB
    ordeq
    ax-mp
    mpbir
    @5
    vx
    vy
    @0
    @3
    @0
    wcel
    @3
    cB
    wcel
    @4
    cB
    wcel
    @5
    @4
    @0
    wcel
    @0
    cB
    @3
    issmo.4
    eleq2i
    @0
    cB
    @4
    issmo.4
    eleq2i
    issmo.3
    syl2anb
    rgen2a
    vx
    vy
    cA
    df-smo
    mpbir3an
end
