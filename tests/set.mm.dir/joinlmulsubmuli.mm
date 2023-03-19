include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "subdiri.mm"
include "eqtri.mm"

theorem joinlmulsubmuli
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x
  assume joinlmulsubmuli.1: |- A e. CC
  assume joinlmulsubmuli.2: |- B e. CC
  assume joinlmulsubmuli.3: |- C e. CC
  assume joinlmulsubmuli.4: |- ( ( A x. B ) - ( C x. B ) ) = D


  assert |- ( ( A - C ) x. B ) = D

  proof
    cA
    cC
    cmin
    co
    cB
    cmul
    co
    cA
    cB
    cmul
    co
    cC
    cB
    cmul
    co
    cmin
    co
    cD
    cA
    cC
    cB
    joinlmulsubmuli.1
    joinlmulsubmuli.3
    joinlmulsubmuli.2
    subdiri
    joinlmulsubmuli.4
    eqtri
end
