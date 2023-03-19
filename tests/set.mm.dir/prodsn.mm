include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "csn.mm"
include "cprod.mm"
include "c1.mm"
include "cmul.mm"
include "cop.mm"
include "cseq.mm"
include "cfv.mm"
include "cv.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvprodi.mm"
include "csbeq1.mm"
include "cn.mm"
include "1nn.mm"
include "a1i.mm"
include "cfz.mm"
include "co.mm"
include "wf1o.mm"
include "cz.mm"
include "1z.mm"
include "f1osng.mm"
include "wceq.mm"
include "wb.mm"
include "fzsn.mm"
include "ax-mp.mm"
include "f1oeq2.mm"
include "sylibr.mm"
include "mpan.mm"
include "adantr.mm"
include "velsn.mm"
include "nfcvd.mm"
include "csbiegf.mm"
include "sylan9eqr.mm"
include "sylan2b.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "eleq2i.mm"
include "bitri.mm"
include "fvsng.mm"
include "csbeq1d.mm"
include "simpr.mm"
include "sylancr.mm"
include "3eqtr4rd.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "fprod.mm"
include "syl5eq.mm"
include "seq1i.mm"
include "eqtrd.mm"

theorem prodsn
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  assume prodsn.1: |- ( k = M -> A = B )

  disjoint B k
  disjoint M k
  disjoint V k
  disjoint A m
  disjoint A n
  disjoint m n
  disjoint B m
  disjoint B n
  disjoint k m
  disjoint k n
  disjoint M m
  disjoint M n
  disjoint V m
  disjoint V n
  assert |- ( ( M e. V /\ B e. CC ) -> prod_ k e. { M } A = B )

  proof
    cM
    cV
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cM
    csn
    #
    cA
    vk
    cprod
    #
    c1
    cmul
    c1
    cB
    cop
    csn
    #
    c1
    cseq
    cfv
    #
    cB
    @2
    @4
    @3
    vk
    vm
    cv
    #
    cA
    csb
    #
    vm
    cprod
    @6
    @3
    cA
    @8
    vk
    vm
    vm
    cA
    nfcv
    vk
    @7
    cA
    nfcsb1v
    vk
    @7
    cA
    csbeq1a
    cbvprodi
    @2
    @3
    @8
    vk
    vn
    cv
    #
    c1
    cM
    cop
    csn
    #
    cfv
    #
    cA
    csb
    #
    vm
    vn
    @10
    @5
    c1
    vk
    @7
    @11
    cA
    csbeq1
    c1
    cn
    wcel
    @2
    1nn
    a1i
    @0
    c1
    c1
    cfz
    co
    #
    @3
    @10
    wf1o
    #
    @1
    c1
    cz
    wcel
    #
    @0
    @14
    1z
    @15
    @0
    wa
    c1
    csn
    #
    @3
    @10
    wf1o
    #
    @14
    c1
    cM
    cz
    cV
    f1osng
    @13
    @16
    wceq
    #
    @14
    @17
    wb
    @15
    @18
    1z
    c1
    fzsn
    ax-mp
    #
    @13
    @16
    @3
    @10
    f1oeq2
    ax-mp
    sylibr
    mpan
    adantr
    @2
    @7
    @3
    wcel
    #
    wa
    @8
    cB
    cc
    @20
    @2
    @7
    cM
    wceq
    #
    @8
    cB
    wceq
    vm
    cM
    velsn
    @21
    @2
    @8
    vk
    cM
    cA
    csb
    #
    cB
    vk
    @7
    cM
    cA
    csbeq1
    @0
    @22
    cB
    wceq
    @1
    vk
    cM
    cA
    cB
    cV
    @0
    vk
    cB
    nfcvd
    prodsn.1
    csbiegf
    adantr
    #
    sylan9eqr
    sylan2b
    @0
    @1
    @20
    simplr
    eqeltrd
    @9
    @13
    wcel
    #
    @2
    @9
    c1
    wceq
    #
    @9
    @5
    cfv
    #
    @12
    wceq
    #
    @24
    @9
    @16
    wcel
    @25
    @13
    @16
    @9
    @19
    eleq2i
    vn
    c1
    velsn
    bitri
    @2
    @25
    @27
    @2
    @27
    @25
    c1
    @5
    cfv
    #
    vk
    c1
    @10
    cfv
    #
    cA
    csb
    #
    wceq
    @2
    @22
    cB
    @30
    @28
    @23
    @2
    vk
    @29
    cM
    cA
    @0
    @29
    cM
    wceq
    #
    @1
    @15
    @0
    @31
    1z
    c1
    cM
    cz
    cV
    fvsng
    mpan
    adantr
    csbeq1d
    @2
    @15
    @1
    @28
    cB
    wceq
    1z
    @0
    @1
    simpr
    c1
    cB
    cz
    cc
    fvsng
    sylancr
    #
    3eqtr4rd
    @25
    @26
    @28
    @12
    @30
    @9
    c1
    @5
    fveq2
    @25
    vk
    @11
    @29
    cA
    @9
    c1
    @10
    fveq2
    csbeq1d
    eqeq12d
    syl5ibrcom
    imp
    sylan2b
    fprod
    syl5eq
    @2
    cB
    cmul
    @5
    c1
    1z
    @32
    seq1i
    eqtrd
end
