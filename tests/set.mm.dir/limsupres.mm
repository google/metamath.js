include "cres.mm"
include "clsp.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "crn.mm"
include "cinf.mm"
include "nfv.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "resimass.mm"
include "a1i.mm"
include "ssrin.mm"
include "syl.mm"
include "adantl.mm"
include "inss2.mm"
include "sstrd.mm"
include "supxrcld.mm"
include "supxrss.mm"
include "syl2anc.mm"
include "infrnmptle.mm"
include "cvv.mm"
include "wceq.mm"
include "resexd.mm"
include "eqid.mm"
include "limsupval.mm"
include "breq12d.mm"
include "mpbird.mm"

theorem limsupres
  let wph: wff ph
  let cC: class C
  let cF: class F
  let cV: class V
  let vk: setvar k
  assume limsupres.1: |- ( ph -> F e. V )


  assert |- ( ph -> ( limsup ` ( F |` C ) ) <_ ( limsup ` F ) )

  proof
    wph
    cF
    cC
    cres
    #
    clsp
    cfv
    #
    cF
    clsp
    cfv
    #
    cle
    wbr
    vk
    cr
    @0
    vk
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    cxr
    clt
    cinf
    #
    vk
    cr
    cF
    @4
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    crn
    cxr
    clt
    cinf
    #
    cle
    wbr
    wph
    vk
    cr
    @7
    @12
    wph
    vk
    nfv
    wph
    @3
    cr
    wcel
    #
    wa
    #
    @6
    @16
    @6
    @11
    cxr
    @15
    @6
    @11
    wss
    #
    wph
    @15
    @5
    @10
    wss
    #
    @17
    @18
    @15
    cF
    cC
    @4
    resimass
    a1i
    @5
    @10
    cxr
    ssrin
    syl
    adantl
    #
    @11
    cxr
    wss
    #
    @16
    @10
    cxr
    inss2
    a1i
    #
    sstrd
    supxrcld
    @16
    @11
    @21
    supxrcld
    @16
    @17
    @20
    @7
    @12
    cle
    wbr
    @19
    @21
    @6
    @11
    supxrss
    syl2anc
    infrnmptle
    wph
    @1
    @9
    @2
    @14
    cle
    wph
    @0
    cvv
    wcel
    @1
    @9
    wceq
    wph
    cF
    cC
    cV
    limsupres.1
    resexd
    vk
    @0
    @8
    cvv
    @8
    eqid
    limsupval
    syl
    wph
    cF
    cV
    wcel
    @2
    @14
    wceq
    limsupres.1
    vk
    cF
    @13
    cV
    @13
    eqid
    limsupval
    syl
    breq12d
    mpbird
end
