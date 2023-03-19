include "wcel.mm"
include "cc.mm"
include "wa.mm"
include "csn.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "cop.mm"
include "cseq.mm"
include "cfv.mm"
include "cv.mm"
include "csb.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "cbvsumi.mm"
include "csbeq1.mm"
include "cn.mm"
include "1nn.mm"
include "a1i.mm"
include "wf1o.mm"
include "cfz.mm"
include "co.mm"
include "simpl.mm"
include "f1osng.mm"
include "sylancr.mm"
include "cz.mm"
include "wceq.mm"
include "wb.mm"
include "1z.mm"
include "fzsn.mm"
include "f1oeq2.mm"
include "mp2b.mm"
include "sylibr.mm"
include "elsni.mm"
include "adantl.mm"
include "csbeq1d.mm"
include "wnfc.mm"
include "csbiegf.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "elfz1eq.mm"
include "fveq2d.mm"
include "fvsng.mm"
include "sylan9eqr.mm"
include "simpr.mm"
include "3eqtr4rd.mm"
include "fsum.mm"
include "syl5eq.mm"
include "seq1i.mm"
include "eqtrd.mm"

theorem sumsnf
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  assume sumsnf.1: |- F/_ k B
  assume sumsnf.2: |- ( k = M -> A = B )

  disjoint M k
  disjoint V k
  disjoint A m
  disjoint A n
  disjoint m n
  disjoint B m
  disjoint B n
  disjoint M m
  disjoint M n
  disjoint k m
  disjoint k n
  disjoint V m
  disjoint V n
  assert |- ( ( M e. V /\ B e. CC ) -> sum_ k e. { M } A = B )

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
    csu
    #
    c1
    caddc
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
    csu
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
    cbvsumi
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
    #
    @2
    1nn
    a1i
    @2
    c1
    csn
    #
    @3
    @10
    wf1o
    #
    c1
    c1
    cfz
    co
    #
    @3
    @10
    wf1o
    #
    @2
    @13
    @0
    @15
    1nn
    @0
    @1
    simpl
    #
    c1
    cM
    cn
    cV
    f1osng
    sylancr
    c1
    cz
    wcel
    @16
    @14
    wceq
    @17
    @15
    wb
    1z
    c1
    fzsn
    @16
    @14
    @3
    @10
    f1oeq2
    mp2b
    sylibr
    @2
    @7
    @3
    wcel
    #
    wa
    #
    @8
    vk
    cM
    cA
    csb
    #
    cc
    @20
    vk
    @7
    cM
    cA
    @19
    @7
    cM
    wceq
    @2
    @7
    cM
    elsni
    adantl
    csbeq1d
    @20
    @21
    cB
    cc
    @0
    @21
    cB
    wceq
    #
    @1
    @19
    vk
    cM
    cA
    cB
    cV
    vk
    cB
    wnfc
    @0
    sumsnf.1
    a1i
    sumsnf.2
    csbiegf
    #
    ad2antrr
    @0
    @1
    @19
    simplr
    eqeltrd
    eqeltrd
    @2
    @9
    @16
    wcel
    #
    wa
    #
    @21
    cB
    @12
    @9
    @5
    cfv
    #
    @0
    @22
    @1
    @24
    @23
    ad2antrr
    @25
    vk
    @11
    cM
    cA
    @24
    @2
    @11
    c1
    @10
    cfv
    #
    cM
    @24
    @9
    c1
    @10
    @9
    c1
    elfz1eq
    #
    fveq2d
    @2
    @13
    @0
    @27
    cM
    wceq
    1nn
    @18
    c1
    cM
    cn
    cV
    fvsng
    sylancr
    sylan9eqr
    csbeq1d
    @24
    @2
    @26
    c1
    @5
    cfv
    #
    cB
    @24
    @9
    c1
    @5
    @28
    fveq2d
    @2
    @13
    @1
    @29
    cB
    wceq
    1nn
    @0
    @1
    simpr
    c1
    cB
    cn
    cc
    fvsng
    sylancr
    #
    sylan9eqr
    3eqtr4rd
    fsum
    syl5eq
    @2
    cB
    caddc
    @5
    c1
    1z
    @30
    seq1i
    eqtrd
end
