include "wcel.mm"
include "csn.mm"
include "ciun.mm"
include "cv.mm"
include "wrex.mm"
include "eliun.mm"
include "nfcri.mm"
include "wceq.mm"
include "eleq2d.mm"
include "rexsngf.mm"
include "syl5bb.mm"
include "eqrdv.mm"

theorem iunxsngf2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y
  assume iunxsngf2.1: |- F/_ x C
  assume iunxsngf2.2: |- ( x = A -> B = C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C y
  disjoint V y
  assert |- ( A e. V -> U_ x e. { A } B = C )

  proof
    cA
    cV
    wcel
    #
    vy
    vx
    cA
    csn
    #
    cB
    ciun
    #
    cC
    vy
    cv
    #
    @2
    wcel
    @3
    cB
    wcel
    #
    vx
    @1
    wrex
    @0
    @3
    cC
    wcel
    #
    vx
    @3
    @1
    cB
    eliun
    @4
    @5
    vx
    cA
    cV
    vx
    vy
    cC
    iunxsngf2.1
    nfcri
    vx
    cv
    cA
    wceq
    cB
    cC
    @3
    iunxsngf2.2
    eleq2d
    rexsngf
    syl5bb
    eqrdv
end
