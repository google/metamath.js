include "csu.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "cbvsum.mm"
include "a1i.mm"
include "wi.mm"
include "nfv.mm"
include "nfeq.mm"
include "nfim.mm"
include "eqeq1.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "eqeq2d.mm"
include "chvar.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "nfan.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "cc.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "fsumf1o.mm"
include "eqcomi.mm"
include "3eqtrd.mm"

theorem fsumf1of
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let vi: setvar i
  let vj: setvar j
  assume fsumf1of.1: |- F/ k ph
  assume fsumf1of.2: |- F/ n ph
  assume fsumf1of.3: |- ( k = G -> B = D )
  assume fsumf1of.4: |- ( ph -> C e. Fin )
  assume fsumf1of.5: |- ( ph -> F : C -1-1-onto-> A )
  assume fsumf1of.6: |- ( ( ph /\ n e. C ) -> ( F ` n ) = G )
  assume fsumf1of.7: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint B n
  disjoint C n
  disjoint D k
  disjoint F n
  disjoint G k
  disjoint k n
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint i k
  disjoint j k
  disjoint B i
  disjoint B j
  disjoint i n
  disjoint j n
  disjoint C j
  disjoint D i
  disjoint D j
  disjoint F j
  disjoint G i
  disjoint i ph
  disjoint j ph
  assert |- ( ph -> sum_ k e. A B = sum_ n e. C D )

  proof
    wph
    cA
    cB
    vk
    csu
    #
    cA
    vk
    vi
    cv
    #
    cB
    csb
    #
    vi
    csu
    #
    cC
    vn
    vj
    cv
    #
    cD
    csb
    #
    vj
    csu
    #
    cC
    cD
    vn
    csu
    #
    @0
    @3
    wceq
    wph
    cA
    cB
    @2
    vk
    vi
    vk
    @1
    cB
    csbeq1a
    #
    vi
    cA
    nfcv
    vk
    cA
    nfcv
    vi
    cB
    nfcv
    vk
    @1
    cB
    nfcsb1v
    #
    cbvsum
    a1i
    wph
    cA
    @2
    cC
    @5
    vi
    vj
    cF
    vn
    @4
    cG
    csb
    #
    vk
    cv
    #
    @10
    wceq
    #
    cB
    @5
    wceq
    #
    wi
    #
    @1
    @10
    wceq
    #
    @2
    @5
    wceq
    #
    wi
    vk
    vi
    @15
    @16
    vk
    @15
    vk
    nfv
    vk
    @2
    @5
    @9
    vk
    @5
    nfcv
    nfeq
    nfim
    @11
    @1
    wceq
    #
    @12
    @15
    @13
    @16
    @11
    @1
    @10
    eqeq1
    @17
    cB
    @2
    @5
    @8
    eqeq1d
    imbi12d
    @11
    cG
    wceq
    #
    cB
    cD
    wceq
    #
    wi
    @14
    vn
    vj
    @12
    @13
    vn
    vn
    @11
    @10
    vn
    @11
    nfcv
    vn
    @4
    cG
    nfcsb1v
    #
    nfeq
    vn
    cB
    @5
    vn
    cB
    nfcv
    vn
    @4
    cD
    nfcsb1v
    #
    nfeq
    nfim
    vn
    cv
    #
    @4
    wceq
    #
    @18
    @12
    @19
    @13
    @23
    cG
    @10
    @11
    vn
    @4
    cG
    csbeq1a
    #
    eqeq2d
    @23
    cD
    @5
    cB
    vn
    @4
    cD
    csbeq1a
    #
    eqeq2d
    imbi12d
    fsumf1of.3
    chvar
    chvar
    fsumf1of.4
    fsumf1of.5
    wph
    @22
    cC
    wcel
    #
    wa
    #
    @22
    cF
    cfv
    #
    cG
    wceq
    #
    wi
    wph
    @4
    cC
    wcel
    #
    wa
    #
    @4
    cF
    cfv
    #
    @10
    wceq
    #
    wi
    vn
    vj
    @31
    @33
    vn
    wph
    @30
    vn
    fsumf1of.2
    @30
    vn
    nfv
    nfan
    vn
    @32
    @10
    vn
    @32
    nfcv
    @20
    nfeq
    nfim
    @23
    @27
    @31
    @29
    @33
    @23
    @26
    @30
    wph
    @22
    @4
    cC
    eleq1
    anbi2d
    @23
    @28
    @32
    cG
    @10
    @22
    @4
    cF
    fveq2
    @24
    eqeq12d
    imbi12d
    fsumf1of.6
    chvar
    wph
    @11
    cA
    wcel
    #
    wa
    #
    cB
    cc
    wcel
    #
    wi
    wph
    @1
    cA
    wcel
    #
    wa
    #
    @2
    cc
    wcel
    #
    wi
    vk
    vi
    @38
    @39
    vk
    wph
    @37
    vk
    fsumf1of.1
    @37
    vk
    nfv
    nfan
    vk
    @2
    cc
    @9
    nfel1
    nfim
    @17
    @35
    @38
    @36
    @39
    @17
    @34
    @37
    wph
    @11
    @1
    cA
    eleq1
    anbi2d
    @17
    cB
    @2
    cc
    @8
    eleq1d
    imbi12d
    fsumf1of.7
    chvar
    fsumf1o
    @6
    @7
    wceq
    wph
    @7
    @6
    cC
    cD
    @5
    vn
    vj
    @25
    vj
    cC
    nfcv
    vn
    cC
    nfcv
    vj
    cD
    nfcv
    @21
    cbvsum
    eqcomi
    a1i
    3eqtrd
end
