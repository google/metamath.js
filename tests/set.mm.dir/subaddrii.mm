include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "subaddi.mm"
include "mpbir.mm"

theorem subaddrii
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidi.1: |- A e. CC
  assume pncan3i.2: |- B e. CC
  assume subadd.3: |- C e. CC
  assume subaddri.4: |- ( B + C ) = A


  assert |- ( A - B ) = C

  proof
    cA
    cB
    cmin
    co
    cC
    wceq
    cB
    cC
    caddc
    co
    cA
    wceq
    subaddri.4
    cA
    cB
    cC
    negidi.1
    pncan3i.2
    subadd.3
    subaddi
    mpbir
end
