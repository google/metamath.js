include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cprod.mm"
include "csn.mm"
include "wceq.mm"
include "fzsn.mm"
include "prodeq1d.mm"
include "adantr.mm"
include "prodsn.mm"
include "eqtrd.mm"

theorem fprod1
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let vm: setvar m
  let vn: setvar n
  let cV: class V
  assume prodsn.1: |- ( k = M -> A = B )

  disjoint B k
  disjoint M k
  disjoint A m
  disjoint A n
  disjoint m n
  disjoint B m
  disjoint B n
  disjoint k m
  disjoint k n
  disjoint M m
  disjoint M n
  disjoint V k
  disjoint V m
  disjoint V n
  assert |- ( ( M e. ZZ /\ B e. CC ) -> prod_ k e. ( M ... M ) A = B )

  proof
    cM
    cz
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    cM
    cM
    cfz
    co
    #
    cA
    vk
    cprod
    #
    cM
    csn
    #
    cA
    vk
    cprod
    #
    cB
    @0
    @3
    @5
    wceq
    @1
    @0
    @2
    @4
    cA
    vk
    cM
    fzsn
    prodeq1d
    adantr
    cA
    cB
    vk
    cM
    cz
    prodsn.1
    prodsn
    eqtrd
end
