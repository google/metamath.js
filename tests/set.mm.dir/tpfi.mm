include "ctp.mm"
include "cpr.mm"
include "csn.mm"
include "cun.mm"
include "cfn.mm"
include "df-tp.mm"
include "wcel.mm"
include "prfi.mm"
include "snfi.mm"
include "unfi.mm"
include "mp2an.mm"
include "eqeltri.mm"

theorem tpfi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- { A , B , C } e. Fin

  proof
    cA
    cB
    cC
    ctp
    cA
    cB
    cpr
    #
    cC
    csn
    #
    cun
    #
    cfn
    cA
    cB
    cC
    df-tp
    @0
    cfn
    wcel
    @1
    cfn
    wcel
    @2
    cfn
    wcel
    cA
    cB
    prfi
    cC
    snfi
    @0
    @1
    unfi
    mp2an
    eqeltri
end
