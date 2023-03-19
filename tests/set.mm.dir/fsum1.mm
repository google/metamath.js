include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "csn.mm"
include "wceq.mm"
include "fzsn.mm"
include "adantr.mm"
include "sumeq1d.mm"
include "sumsn.mm"
include "eqtrd.mm"

theorem fsum1
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let vm: setvar m
  let vn: setvar n
  let cV: class V
  assume fsum1.1: |- ( k = M -> A = B )

  disjoint B k
  disjoint M k
  disjoint m n
  disjoint A m
  disjoint A n
  disjoint k m
  disjoint k n
  disjoint B m
  disjoint B n
  disjoint M m
  disjoint M n
  disjoint V k
  disjoint V m
  disjoint V n
  assert |- ( ( M e. ZZ /\ B e. CC ) -> sum_ k e. ( M ... M ) A = B )

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
    #
    cM
    cM
    cfz
    co
    #
    cA
    vk
    csu
    cM
    csn
    #
    cA
    vk
    csu
    cB
    @2
    @3
    @4
    cA
    vk
    @0
    @3
    @4
    wceq
    @1
    cM
    fzsn
    adantr
    sumeq1d
    cA
    cB
    vk
    cM
    cz
    fsum1.1
    sumsn
    eqtrd
end
