include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "crmx.mm"
include "cmul.mm"
include "cexp.mm"
include "c1.mm"
include "cmin.mm"
include "crmy.mm"
include "wceq.mm"
include "rmxyadd.mm"
include "simprd.mm"

theorem rmyadd
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( A e. ( ZZ>= ` 2 ) /\ M e. ZZ /\ N e. ZZ ) -> ( A rmY ( M + N ) ) = ( ( ( A rmY M ) x. ( A rmX N ) ) + ( ( A rmX M ) x. ( A rmY N ) ) ) )

  proof
    cA
    c2
    cuz
    cfv
    wcel
    cM
    cz
    wcel
    cN
    cz
    wcel
    w3a
    cA
    cM
    cN
    caddc
    co
    #
    crmx
    co
    cA
    cM
    crmx
    co
    #
    cA
    cN
    crmx
    co
    #
    cmul
    co
    cA
    c2
    cexp
    co
    c1
    cmin
    co
    cA
    cM
    crmy
    co
    #
    cA
    cN
    crmy
    co
    #
    cmul
    co
    cmul
    co
    caddc
    co
    wceq
    cA
    @0
    crmy
    co
    @3
    @2
    cmul
    co
    @1
    @4
    cmul
    co
    caddc
    co
    wceq
    cA
    cM
    cN
    rmxyadd
    simprd
end
