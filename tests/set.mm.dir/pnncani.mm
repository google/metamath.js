include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "pnncan.mm"
include "mp3an.mm"

theorem pnncani
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC
  assume subadd.3: |- C e. CC


  assert |- ( ( A + B ) - ( A - C ) ) = ( B + C )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cA
    cB
    caddc
    co
    cA
    cC
    cmin
    co
    cmin
    co
    cB
    cC
    caddc
    co
    wceq
    negidi.1
    pncan3i.2
    subadd.3
    cA
    cB
    cC
    pnncan
    mp3an
end
