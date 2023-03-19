include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "wceq.mm"
include "addsub4.mm"
include "mp4an.mm"

theorem addsub4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC
  assume subadd.3: |- C e. CC
  assume addsub4i.4: |- D e. CC


  assert |- ( ( A + B ) - ( C + D ) ) = ( ( A - C ) + ( B - D ) )

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
    cmin
    co
    cA
    cC
    cmin
    co
    cB
    cD
    cmin
    co
    caddc
    co
    wceq
    negidi.1
    pncan3i.2
    subadd.3
    addsub4i.4
    cA
    cB
    cC
    cD
    addsub4
    mp4an
end
