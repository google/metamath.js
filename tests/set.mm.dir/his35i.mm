include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "csp.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "wceq.mm"
include "his35.mm"
include "mp4an.mm"

theorem his35i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume his35.1: |- A e. CC
  assume his35.2: |- B e. CC
  assume his35.3: |- C e. ~H
  assume his35.4: |- D e. ~H


  assert |- ( ( A .h C ) .ih ( B .h D ) ) = ( ( A x. ( * ` B ) ) x. ( C .ih D ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    chil
    wcel
    cD
    chil
    wcel
    cA
    cC
    csm
    co
    cB
    cD
    csm
    co
    csp
    co
    cA
    cB
    ccj
    cfv
    cmul
    co
    cC
    cD
    csp
    co
    cmul
    co
    wceq
    his35.1
    his35.2
    his35.3
    his35.4
    cA
    cB
    cC
    cD
    his35
    mp4an
end
