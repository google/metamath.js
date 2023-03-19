include "wss.mm"
include "cdif.mm"
include "wrex.mm"
include "wral.mm"
include "ciun.mm"
include "wa.mm"
include "wceq.mm"
include "iunss2.mm"
include "difss.mm"
include "iunss1.mm"
include "ax-mp.mm"
include "cbviunv.mm"
include "sseqtr4i.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"

theorem iunxdif2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume iunxdif2.1: |- ( x = y -> C = D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint D x
  assert |- ( A. x e. A E. y e. ( A \ B ) C C_ D -> U_ y e. ( A \ B ) D = U_ x e. A C )

  proof
    cC
    cD
    wss
    vy
    cA
    cB
    cdif
    #
    wrex
    vx
    cA
    wral
    #
    vy
    @0
    cD
    ciun
    #
    vx
    cA
    cC
    ciun
    #
    wss
    #
    @3
    @2
    wss
    #
    wa
    @2
    @3
    wceq
    @1
    @5
    @4
    vx
    vy
    cA
    @0
    cC
    cD
    iunss2
    @2
    vy
    cA
    cD
    ciun
    #
    @3
    @0
    cA
    wss
    @2
    @6
    wss
    cA
    cB
    difss
    vy
    @0
    cA
    cD
    iunss1
    ax-mp
    vx
    vy
    cA
    cC
    cD
    iunxdif2.1
    cbviunv
    sseqtr4i
    jctil
    @2
    @3
    eqss
    sylibr
end
