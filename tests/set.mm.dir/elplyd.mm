include "cc.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "csn.mm"
include "cun.mm"
include "cply.mm"
include "cfv.mm"
include "cn0.mm"
include "wcel.mm"
include "cif.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfov.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "cbvsumi.mm"
include "wa.mm"
include "elfznn0.mm"
include "adantl.mm"
include "iftrue.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "syl5eq.mm"
include "mpteq2dv.mm"
include "wss.mm"
include "wf.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "elun1.mm"
include "syl.mm"
include "adantlr.mm"
include "wn.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snss.mm"
include "mpbir.mm"
include "a1i.mm"
include "ifclda.mm"
include "fmptd.mm"
include "elplyr.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "plyun0.mm"
include "syl6eleq.mm"

theorem elplyd
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cN: class N
  let vj: setvar j
  assume elplyd.1: |- ( ph -> S C_ CC )
  assume elplyd.2: |- ( ph -> N e. NN0 )
  assume elplyd.3: |- ( ( ph /\ k e. ( 0 ... N ) ) -> A e. S )

  disjoint A z
  disjoint k z
  disjoint N k
  disjoint N z
  disjoint k ph
  disjoint ph z
  disjoint S k
  disjoint S z
  disjoint j z
  disjoint A j
  disjoint j k
  disjoint N j
  disjoint S j
  assert |- ( ph -> ( z e. CC |-> sum_ k e. ( 0 ... N ) ( A x. ( z ^ k ) ) ) e. ( Poly ` S ) )

  proof
    wph
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    cA
    vz
    cv
    #
    vk
    cv
    #
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    cS
    cc0
    csn
    #
    cun
    #
    cply
    cfv
    #
    cS
    cply
    cfv
    wph
    vz
    cc
    @0
    vj
    cv
    #
    vk
    cn0
    @2
    @0
    wcel
    #
    cA
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    @1
    @10
    cexp
    co
    #
    cmul
    co
    #
    vj
    csu
    #
    cmpt
    #
    @6
    @9
    wph
    vz
    cc
    @17
    @5
    wph
    @17
    @0
    @2
    @13
    cfv
    #
    @3
    cmul
    co
    #
    vk
    csu
    @5
    @0
    @16
    @20
    vj
    vk
    vk
    @14
    @15
    cmul
    vk
    cn0
    @12
    @10
    nffvmpt1
    vk
    cmul
    nfcv
    vk
    @15
    nfcv
    nfov
    vj
    @20
    nfcv
    @10
    @2
    wceq
    @14
    @19
    @15
    @3
    cmul
    @10
    @2
    @13
    fveq2
    @10
    @2
    @1
    cexp
    oveq2
    oveq12d
    cbvsumi
    wph
    @0
    @20
    @4
    vk
    wph
    @11
    wa
    #
    @19
    cA
    @3
    cmul
    @21
    @19
    @12
    cA
    @21
    @2
    cn0
    wcel
    #
    @12
    cS
    wcel
    @19
    @12
    wceq
    @11
    @22
    wph
    @2
    cN
    elfznn0
    adantl
    @21
    @12
    cA
    cS
    @11
    @12
    cA
    wceq
    wph
    @11
    cA
    cc0
    iftrue
    adantl
    #
    elplyd.3
    eqeltrd
    vk
    cn0
    @12
    cS
    @13
    @13
    eqid
    #
    fvmpt2
    syl2anc
    @23
    eqtrd
    oveq1d
    sumeq2dv
    syl5eq
    mpteq2dv
    wph
    @8
    cc
    wss
    cN
    cn0
    wcel
    cn0
    @8
    @13
    wf
    @18
    @9
    wcel
    wph
    cS
    @7
    cc
    elplyd.1
    wph
    cc0
    cc
    wph
    0cnd
    snssd
    unssd
    elplyd.2
    wph
    vk
    cn0
    @12
    @8
    @13
    wph
    @22
    wa
    #
    @11
    cA
    cc0
    @8
    wph
    @11
    cA
    @8
    wcel
    #
    @22
    @21
    cA
    cS
    wcel
    @26
    elplyd.3
    cA
    cS
    @7
    elun1
    syl
    adantlr
    cc0
    @8
    wcel
    #
    @25
    @11
    wn
    wa
    @27
    @7
    @8
    wss
    @7
    cS
    ssun2
    cc0
    @8
    c0ex
    snss
    mpbir
    a1i
    ifclda
    @24
    fmptd
    vz
    @13
    @8
    vj
    cN
    elplyr
    syl3anc
    eqeltrrd
    cS
    plyun0
    syl6eleq
end
