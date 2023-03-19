include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "wtru.mm"
include "cc.mm"
include "wcel.mm"
include "a1i.mm"
include "joinlmuladdmuld.mm"
include "trud.mm"

theorem joinlmuladdmuli
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x
  assume joinlmuladdmuli.1: |- A e. CC
  assume joinlmuladdmuli.2: |- B e. CC
  assume joinlmuladdmuli.3: |- C e. CC
  assume joinlmuladdmuli.4: |- ( ( A x. B ) + ( C x. B ) ) = D


  assert |- ( ( A + C ) x. B ) = D

  proof
    cA
    cC
    caddc
    co
    cB
    cmul
    co
    cD
    wceq
    wtru
    cA
    cB
    cC
    cD
    cA
    cc
    wcel
    wtru
    joinlmuladdmuli.1
    a1i
    cB
    cc
    wcel
    wtru
    joinlmuladdmuli.2
    a1i
    cC
    cc
    wcel
    wtru
    joinlmuladdmuli.3
    a1i
    cA
    cB
    cmul
    co
    cC
    cB
    cmul
    co
    caddc
    co
    cD
    wceq
    wtru
    joinlmuladdmuli.4
    a1i
    joinlmuladdmuld
    trud
end
