include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "inidm.mm"
include "oveq2i.mm"
include "wceq.mm"
include "chabs1.mm"
include "anidms.mm"
include "syl5eqr.mm"

theorem chjidm
  let cA: class A


  assert |- ( A e. CH -> ( A vH A ) = A )

  proof
    cA
    cch
    wcel
    #
    cA
    cA
    chj
    co
    cA
    cA
    cA
    cin
    #
    chj
    co
    #
    cA
    @1
    cA
    cA
    chj
    cA
    inidm
    oveq2i
    @0
    @2
    cA
    wceq
    cA
    cA
    chabs1
    anidms
    syl5eqr
end
