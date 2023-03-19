include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "ccoe.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cuz.mm"
include "cima.mm"
include "cc0.mm"
include "csn.mm"
include "wceq.mm"
include "cdgr.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wn.mm"
include "cif.mm"
include "cmpt.mm"
include "coeeq2.mm"
include "ad2antrr.mm"
include "fveq1d.mm"
include "nfcv.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "nfim.mm"
include "breq1.mm"
include "notbid.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "cid.mm"
include "iffalse.mm"
include "fveq2d.mm"
include "cc.mm"
include "0cn.mm"
include "fvi.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqid.mm"
include "fvmpt2i.mm"
include "syl5ibr.mm"
include "vtoclgaf.mm"
include "imp.mm"
include "adantll.mm"
include "eqtrd.mm"
include "ex.mm"
include "necon1ad.mm"
include "ralrimiva.mm"
include "wf.mm"
include "wb.mm"
include "coef3.mm"
include "syl.mm"
include "plyco0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "dgrlb.mm"
include "syl3anc.mm"

theorem dgrle
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let vm: setvar m
  assume dgrle.1: |- ( ph -> F e. ( Poly ` S ) )
  assume dgrle.2: |- ( ph -> N e. NN0 )
  assume dgrle.3: |- ( ( ph /\ k e. ( 0 ... N ) ) -> A e. CC )
  assume dgrle.4: |- ( ph -> F = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( A x. ( z ^ k ) ) ) )

  disjoint A z
  disjoint k z
  disjoint N k
  disjoint N z
  disjoint k ph
  disjoint ph z
  disjoint m z
  disjoint A m
  disjoint F m
  disjoint k m
  disjoint N m
  disjoint m ph
  assert |- ( ph -> ( deg ` F ) <_ N )

  proof
    wph
    cF
    cS
    cply
    cfv
    wcel
    #
    cN
    cn0
    wcel
    #
    cF
    ccoe
    cfv
    #
    cN
    c1
    caddc
    co
    cuz
    cfv
    cima
    cc0
    csn
    wceq
    #
    cF
    cdgr
    cfv
    #
    cN
    cle
    wbr
    dgrle.1
    dgrle.2
    wph
    @3
    vm
    cv
    #
    @2
    cfv
    #
    cc0
    wne
    @5
    cN
    cle
    wbr
    #
    wi
    #
    vm
    cn0
    wral
    #
    wph
    @8
    vm
    cn0
    wph
    @5
    cn0
    wcel
    #
    wa
    #
    @7
    @6
    cc0
    @11
    @7
    wn
    #
    @6
    cc0
    wceq
    @11
    @12
    wa
    #
    @6
    @5
    vk
    cn0
    vk
    cv
    #
    cN
    cle
    wbr
    #
    cA
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    cc0
    @13
    @5
    @2
    @17
    wph
    @2
    @17
    wceq
    @10
    @12
    wph
    vz
    cA
    cS
    vk
    cF
    cN
    dgrle.1
    dgrle.2
    dgrle.3
    dgrle.4
    coeeq2
    ad2antrr
    fveq1d
    @10
    @12
    @18
    cc0
    wceq
    #
    wph
    @10
    @12
    @19
    @15
    wn
    #
    @14
    @17
    cfv
    #
    cc0
    wceq
    #
    wi
    @12
    @19
    wi
    vk
    @5
    cn0
    vk
    @5
    nfcv
    @12
    @19
    vk
    @12
    vk
    nfv
    vk
    @18
    cc0
    vk
    cn0
    @16
    @5
    nffvmpt1
    nfeq1
    nfim
    @14
    @5
    wceq
    #
    @20
    @12
    @22
    @19
    @23
    @15
    @7
    @14
    @5
    cN
    cle
    breq1
    notbid
    @23
    @21
    @18
    cc0
    @14
    @5
    @17
    fveq2
    eqeq1d
    imbi12d
    @20
    @22
    @14
    cn0
    wcel
    #
    @16
    cid
    cfv
    #
    cc0
    wceq
    @20
    @25
    cc0
    cid
    cfv
    #
    cc0
    @20
    @16
    cc0
    cid
    @15
    cA
    cc0
    iffalse
    fveq2d
    cc0
    cc
    wcel
    @26
    cc0
    wceq
    0cn
    cc0
    cc
    fvi
    ax-mp
    syl6eq
    @24
    @21
    @25
    cc0
    vk
    cn0
    @16
    @17
    @17
    eqid
    fvmpt2i
    eqeq1d
    syl5ibr
    vtoclgaf
    imp
    adantll
    eqtrd
    ex
    necon1ad
    ralrimiva
    wph
    @1
    cn0
    cc
    @2
    wf
    #
    @3
    @9
    wb
    dgrle.2
    wph
    @0
    @27
    dgrle.1
    @2
    cS
    cF
    @2
    eqid
    #
    coef3
    syl
    @2
    vm
    cN
    plyco0
    syl2anc
    mpbird
    @2
    cS
    cF
    cN
    @4
    @28
    @4
    eqid
    dgrlb
    syl3anc
end
