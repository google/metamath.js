include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cneg.mm"
include "crmx.mm"
include "co.mm"
include "wceq.mm"
include "crmy.mm"
include "rmxyneg.mm"
include "simprd.mm"

theorem rmyneg
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ N e. ZZ ) -> ( A rmY -u N ) = -u ( A rmY N ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    wa
    cA
    cN
    cneg
    #
    crmx
    co
    cA
    cN
    crmx
    co
    wceq
    cA
    @0
    crmy
    co
    cA
    cN
    crmy
    co
    cneg
    wceq
    cA
    cN
    rmxyneg
    simprd
end
