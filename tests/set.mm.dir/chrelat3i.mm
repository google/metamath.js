include "cch.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wi.mm"
include "cat.mm"
include "wral.mm"
include "wb.mm"
include "chrelat3.mm"
include "mp2an.mm"

theorem chrelat3i
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume chrelat3.1: |- A e. CH
  assume chrelat3.2: |- B e. CH

  disjoint A x
  disjoint B x
  assert |- ( A C_ B <-> A. x e. HAtoms ( x C_ A -> x C_ B ) )

  proof
    cA
    cch
    wcel
    cB
    cch
    wcel
    cA
    cB
    wss
    vx
    cv
    #
    cA
    wss
    @0
    cB
    wss
    wi
    vx
    cat
    wral
    wb
    chrelat3.1
    chrelat3.2
    vx
    cA
    cB
    chrelat3
    mp2an
end
