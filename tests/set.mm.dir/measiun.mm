include "cfv.mm"
include "cn.mm"
include "ciun.mm"
include "cesum.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cxr.mm"
include "iccssxr.mm"
include "cmeas.mm"
include "wcel.mm"
include "measvxrge0.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wral.mm"
include "measbase.mm"
include "syl.mm"
include "ralrimiva.mm"
include "sigaclcu2.mm"
include "cvv.mm"
include "nnex.mm"
include "cv.mm"
include "wa.mm"
include "adantr.mm"
include "nfcv.mm"
include "esumcl.mm"
include "sylancr.mm"
include "measssd.mm"
include "c1.mm"
include "cfzo.mm"
include "csb.mm"
include "cdif.mm"
include "cle.mm"
include "nfcsb1v.mm"
include "csbeq1a.mm"
include "wceq.mm"
include "eqidd.mm"
include "orcd.mm"
include "measiuns.mm"
include "a1i.mm"
include "wi.mm"
include "nfv.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "ex.mm"
include "chvar.mm"
include "ralrimiv.mm"
include "wss.mm"
include "fzossnn.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "sigaclfu2.mm"
include "sylan2.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "difssd.mm"
include "esumle.mm"
include "eqbrtrd.mm"
include "xrletrd.mm"

theorem measiun
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vn: setvar n
  let cM: class M
  let vk: setvar k
  let vm: setvar m
  assume measiun.1: |- ( ph -> M e. ( measures ` S ) )
  assume measiun.2: |- ( ph -> A e. S )
  assume measiun.3: |- ( ( ph /\ n e. NN ) -> B e. S )
  assume measiun.4: |- ( ph -> A C_ U_ n e. NN B )

  disjoint n ph
  disjoint S n
  disjoint M n
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint k ph
  disjoint S k
  disjoint B k
  assert |- ( ph -> ( M ` A ) <_ sum* n e. NN ( M ` B ) )

  proof
    wph
    cA
    cM
    cfv
    #
    vn
    cn
    cB
    ciun
    #
    cM
    cfv
    #
    cn
    cB
    cM
    cfv
    #
    vn
    cesum
    #
    wph
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @0
    cc0
    cpnf
    iccssxr
    #
    wph
    cM
    cS
    cmeas
    cfv
    wcel
    #
    cA
    cS
    wcel
    @0
    @5
    wcel
    measiun.1
    measiun.2
    cA
    cS
    cM
    measvxrge0
    syl2anc
    sseldi
    wph
    @5
    cxr
    @2
    @6
    wph
    @7
    @1
    cS
    wcel
    #
    @2
    @5
    wcel
    measiun.1
    wph
    cS
    csiga
    crn
    cuni
    wcel
    #
    cB
    cS
    wcel
    #
    vn
    cn
    wral
    @8
    wph
    @7
    @9
    measiun.1
    cS
    cM
    measbase
    syl
    #
    wph
    @10
    vn
    cn
    measiun.3
    ralrimiva
    cB
    cS
    vn
    sigaclcu2
    syl2anc
    #
    @1
    cS
    cM
    measvxrge0
    syl2anc
    sseldi
    wph
    @5
    cxr
    @4
    @6
    wph
    cn
    cvv
    wcel
    #
    @3
    @5
    wcel
    #
    vn
    cn
    wral
    @4
    @5
    wcel
    nnex
    wph
    @14
    vn
    cn
    wph
    vn
    cv
    #
    cn
    wcel
    #
    wa
    #
    @7
    @10
    @14
    wph
    @7
    @16
    measiun.1
    adantr
    #
    measiun.3
    cB
    cS
    cM
    measvxrge0
    syl2anc
    #
    ralrimiva
    cn
    @3
    vn
    cvv
    vn
    cn
    nfcv
    esumcl
    sylancr
    sseldi
    wph
    cA
    @1
    cS
    cM
    measiun.1
    measiun.2
    @12
    measiun.4
    measssd
    wph
    @2
    cn
    cB
    vk
    c1
    @15
    cfzo
    co
    #
    vn
    vk
    cv
    #
    cB
    csb
    #
    ciun
    #
    cdif
    #
    cM
    cfv
    #
    vn
    cesum
    @4
    cle
    wph
    cB
    @22
    cS
    vk
    vn
    vm
    cv
    #
    cM
    cn
    vn
    @21
    cB
    nfcsb1v
    #
    vn
    @21
    cB
    csbeq1a
    #
    wph
    cn
    cn
    wceq
    cn
    c1
    @26
    cfzo
    co
    wceq
    wph
    cn
    eqidd
    orcd
    measiun.1
    measiun.3
    measiuns
    wph
    cn
    @25
    @3
    vn
    cvv
    @13
    wph
    nnex
    a1i
    @17
    @7
    @24
    cS
    wcel
    #
    @25
    @5
    wcel
    @18
    @17
    @9
    @10
    @23
    cS
    wcel
    #
    @29
    wph
    @9
    @16
    @11
    adantr
    measiun.3
    wph
    @30
    @16
    wph
    @9
    @22
    cS
    wcel
    #
    vk
    cn
    wral
    #
    @30
    @11
    wph
    @31
    vk
    cn
    wph
    @16
    @10
    wi
    #
    wi
    wph
    @21
    cn
    wcel
    #
    @31
    wi
    #
    wi
    vn
    vk
    wph
    @35
    vn
    wph
    vn
    nfv
    @34
    @31
    vn
    vn
    @21
    cn
    vn
    @21
    nfcv
    nfel1
    vn
    @22
    cS
    @27
    nfel1
    nfim
    nfim
    @15
    @21
    wceq
    #
    @33
    @35
    wph
    @36
    @16
    @34
    @10
    @31
    @15
    @21
    cn
    eleq1
    @36
    cB
    @22
    cS
    @28
    eleq1d
    imbi12d
    imbi2d
    wph
    @16
    @10
    measiun.3
    ex
    chvar
    ralrimiv
    @32
    @9
    @31
    vk
    @20
    wral
    #
    @30
    @20
    cn
    wss
    @32
    @37
    wi
    @15
    fzossnn
    @31
    vk
    @20
    cn
    ssralv
    ax-mp
    @22
    cS
    vk
    @15
    sigaclfu2
    sylan2
    syl2anc
    adantr
    cB
    @23
    cS
    difelsiga
    syl3anc
    #
    @24
    cS
    cM
    measvxrge0
    syl2anc
    @19
    @17
    @24
    cB
    cS
    cM
    @18
    @38
    measiun.3
    @17
    cB
    @23
    difssd
    measssd
    esumle
    eqbrtrd
    xrletrd
end
