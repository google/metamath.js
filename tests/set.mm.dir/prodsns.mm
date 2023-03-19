include "wcel.mm"
include "csb.mm"
include "cc.mm"
include "wa.mm"
include "csn.mm"
include "cprod.mm"
include "cv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvprodi.mm"
include "csbeq1.mm"
include "prodsn.mm"
include "syl5eq.mm"

theorem prodsns
  let cA: class A
  let vk: setvar k
  let cM: class M
  let cV: class V
  let vn: setvar n

  disjoint M k
  disjoint A n
  disjoint k n
  disjoint M n
  disjoint V n
  assert |- ( ( M e. V /\ [_ M / k ]_ A e. CC ) -> prod_ k e. { M } A = [_ M / k ]_ A )

  proof
    cM
    cV
    wcel
    vk
    cM
    cA
    csb
    #
    cc
    wcel
    wa
    cM
    csn
    #
    cA
    vk
    cprod
    @1
    vk
    vn
    cv
    #
    cA
    csb
    #
    vn
    cprod
    @0
    @1
    cA
    @3
    vk
    vn
    vn
    cA
    nfcv
    vk
    @2
    cA
    nfcsb1v
    vk
    @2
    cA
    csbeq1a
    cbvprodi
    @3
    @0
    vn
    cM
    cV
    vk
    @2
    cM
    cA
    csbeq1
    prodsn
    syl5eq
end
