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
include "wcel.mm"
include "1nn.mm"
include "a1i.mm"
include "wf1o.mm"
include "cfz.mm"
include "co.mm"
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
include "wa.mm"
include "cc.mm"
include "elsni.mm"
include "adantl.mm"
include "csbeq1d.mm"
include "csbiedf.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "elfz1eq.mm"
include "fveq2d.mm"
include "fvsng.mm"
include "sylan9eqr.mm"
include "3eqtr4rd.mm"
include "fsum.mm"
include "syl5eq.mm"
include "seq1i.mm"
include "eqtrd.mm"

theorem sumsnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  assume sumsnd.1: |- ( ph -> F/_ k B )
  assume sumsnd.2: |- F/ k ph
  assume sumsnd.3: |- ( ( ph /\ k = M ) -> A = B )
  assume sumsnd.4: |- ( ph -> M e. V )
  assume sumsnd.5: |- ( ph -> B e. CC )

  disjoint M k
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint M m
  disjoint M n
  disjoint A m
  disjoint A n
  disjoint B m
  disjoint B n
  disjoint m ph
  disjoint n ph
  assert |- ( ph -> sum_ k e. { M } A = B )

  proof
    wph
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
    wph
    @1
    @0
    vk
    vm
    cv
    #
    cA
    csb
    #
    vm
    csu
    @3
    @0
    cA
    @5
    vk
    vm
    vm
    cA
    nfcv
    vk
    @4
    cA
    nfcsb1v
    vk
    @4
    cA
    csbeq1a
    cbvsumi
    wph
    @0
    @5
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
    @7
    @2
    c1
    vk
    @4
    @8
    cA
    csbeq1
    c1
    cn
    wcel
    #
    wph
    1nn
    a1i
    wph
    c1
    csn
    #
    @0
    @7
    wf1o
    #
    c1
    c1
    cfz
    co
    #
    @0
    @7
    wf1o
    #
    wph
    @10
    cM
    cV
    wcel
    #
    @12
    1nn
    sumsnd.4
    c1
    cM
    cn
    cV
    f1osng
    sylancr
    c1
    cz
    wcel
    @13
    @11
    wceq
    @14
    @12
    wb
    1z
    c1
    fzsn
    @13
    @11
    @0
    @7
    f1oeq2
    mp2b
    sylibr
    wph
    @4
    @0
    wcel
    #
    wa
    #
    @5
    vk
    cM
    cA
    csb
    #
    cc
    @17
    vk
    @4
    cM
    cA
    @16
    @4
    cM
    wceq
    wph
    @4
    cM
    elsni
    adantl
    csbeq1d
    @17
    @18
    cB
    cc
    wph
    @18
    cB
    wceq
    #
    @16
    wph
    vk
    cM
    cA
    cB
    cV
    sumsnd.2
    sumsnd.1
    sumsnd.4
    sumsnd.3
    csbiedf
    #
    adantr
    wph
    cB
    cc
    wcel
    #
    @16
    sumsnd.5
    adantr
    eqeltrd
    eqeltrd
    wph
    @6
    @13
    wcel
    #
    wa
    #
    @18
    cB
    @9
    @6
    @2
    cfv
    #
    wph
    @19
    @22
    @20
    adantr
    @23
    vk
    @8
    cM
    cA
    @22
    wph
    @8
    c1
    @7
    cfv
    #
    cM
    @22
    @6
    c1
    @7
    @6
    c1
    elfz1eq
    #
    fveq2d
    wph
    @10
    @15
    @25
    cM
    wceq
    1nn
    sumsnd.4
    c1
    cM
    cn
    cV
    fvsng
    sylancr
    sylan9eqr
    csbeq1d
    @22
    wph
    @24
    c1
    @2
    cfv
    #
    cB
    @22
    @6
    c1
    @2
    @26
    fveq2d
    wph
    @10
    @21
    @27
    cB
    wceq
    1nn
    sumsnd.5
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
    wph
    cB
    caddc
    @2
    c1
    1z
    @28
    seq1i
    eqtrd
end
