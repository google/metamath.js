include "wcel.mm"
include "csn.mm"
include "ciin.mm"
include "cv.mm"
include "wral.mm"
include "cab.mm"
include "df-iin.mm"
include "wceq.mm"
include "eleq2d.mm"
include "ralsng.mm"
include "abbi1dv.mm"
include "syl5eq.mm"

theorem iinxsng
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y
  assume iinxsng.1: |- ( x = A -> B = C )

  disjoint A x
  disjoint C x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint V y
  assert |- ( A e. V -> |^|_ x e. { A } B = C )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    csn
    #
    cB
    ciin
    vy
    cv
    #
    cB
    wcel
    #
    vx
    @1
    wral
    #
    vy
    cab
    cC
    vx
    vy
    @1
    cB
    df-iin
    @0
    @4
    vy
    cC
    @3
    @2
    cC
    wcel
    vx
    cA
    cV
    vx
    cv
    cA
    wceq
    cB
    cC
    @2
    iinxsng.1
    eleq2d
    ralsng
    abbi1dv
    syl5eq
end
