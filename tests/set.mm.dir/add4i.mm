include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "add4.mm"
include "mp4an.mm"

theorem add4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume add.1: |- A e. CC
  assume add.2: |- B e. CC
  assume add.3: |- C e. CC
  assume add4.4: |- D e. CC


  assert |- ( ( A + B ) + ( C + D ) ) = ( ( A + C ) + ( B + D ) )

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
    cD
    cc
    wcel
    cA
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    caddc
    co
    cA
    cC
    caddc
    co
    cB
    cD
    caddc
    co
    caddc
    co
    wceq
    add.1
    add.2
    add.3
    add4.4
    cA
    cB
    cC
    cD
    add4
    mp4an
end
