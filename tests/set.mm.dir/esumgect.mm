include "cn.mm"
include "cesum.mm"
include "c1.mm"
include "cv.mm"
include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "esumsup.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfan.mm"
include "simpr.mm"
include "simplll.mm"
include "simplr.mm"
include "syl2anc.mm"
include "eqbrtrd.mm"
include "wrex.mm"
include "eqid.mm"
include "esumex.mm"
include "elrnmpti.mm"
include "biimpi.mm"
include "adantl.mm"
include "r19.29af.mm"
include "ralrimiva.mm"
include "wss.mm"
include "wb.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "cvv.mm"
include "ovexd.mm"
include "simpll.mm"
include "fz1ssnn.mm"
include "a1i.mm"
include "sselda.mm"
include "esumcl.mm"
include "rnmptss.mm"
include "syl.mm"
include "iccssxr.mm"
include "syl6ss.mm"
include "sseldi.mm"
include "supxrleub.mm"
include "mpbird.mm"

theorem esumgect
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  assume esumsup.1: |- ( ph -> B e. ( 0 [,] +oo ) )
  assume esumsup.2: |- ( ( ph /\ k e. NN ) -> A e. ( 0 [,] +oo ) )
  assume esumgect.1: |- ( ( ph /\ n e. NN ) -> sum* k e. ( 1 ... n ) A <_ B )

  disjoint A n
  disjoint B n
  disjoint k n
  disjoint k ph
  disjoint n ph
  disjoint A z
  disjoint n z
  disjoint B z
  disjoint k z
  disjoint ph z
  assert |- ( ph -> sum* k e. NN A <_ B )

  proof
    wph
    cn
    cA
    vk
    cesum
    vn
    cn
    c1
    vn
    cv
    #
    cfz
    co
    #
    cA
    vk
    cesum
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cB
    cle
    wph
    cA
    cB
    vk
    vn
    esumsup.1
    esumsup.2
    esumsup
    wph
    @5
    cB
    cle
    wbr
    #
    vz
    cv
    #
    cB
    cle
    wbr
    #
    vz
    @4
    wral
    #
    wph
    @8
    vz
    @4
    wph
    @7
    @4
    wcel
    #
    wa
    #
    @7
    @2
    wceq
    #
    @8
    vn
    cn
    wph
    @10
    vn
    wph
    vn
    nfv
    vn
    @7
    @4
    vn
    @7
    nfcv
    vn
    @3
    vn
    cn
    @2
    nfmpt1
    nfrn
    nfel
    nfan
    @11
    @0
    cn
    wcel
    #
    wa
    #
    @12
    wa
    #
    @7
    @2
    cB
    cle
    @14
    @12
    simpr
    @15
    wph
    @13
    @2
    cB
    cle
    wbr
    wph
    @10
    @13
    @12
    simplll
    @11
    @13
    @12
    simplr
    esumgect.1
    syl2anc
    eqbrtrd
    @10
    @12
    vn
    cn
    wrex
    #
    wph
    @10
    @16
    vn
    cn
    @2
    @7
    @3
    @3
    eqid
    #
    @1
    cA
    vk
    esumex
    elrnmpti
    biimpi
    adantl
    r19.29af
    ralrimiva
    wph
    @4
    cxr
    wss
    cB
    cxr
    wcel
    @6
    @9
    wb
    wph
    @4
    cc0
    cpnf
    cicc
    co
    #
    cxr
    wph
    @2
    @18
    wcel
    #
    vn
    cn
    wral
    @4
    @18
    wss
    wph
    @19
    vn
    cn
    wph
    @13
    wa
    #
    @1
    cvv
    wcel
    cA
    @18
    wcel
    #
    vk
    @1
    wral
    @19
    @20
    c1
    @0
    cfz
    ovexd
    @20
    @21
    vk
    @1
    @20
    vk
    cv
    #
    @1
    wcel
    #
    wa
    wph
    @22
    cn
    wcel
    @21
    wph
    @13
    @23
    simpll
    @20
    @1
    cn
    @22
    @1
    cn
    wss
    @20
    @0
    fz1ssnn
    a1i
    sselda
    esumsup.2
    syl2anc
    ralrimiva
    @1
    cA
    vk
    cvv
    vk
    @1
    nfcv
    esumcl
    syl2anc
    ralrimiva
    vn
    cn
    @2
    @18
    @3
    @17
    rnmptss
    syl
    cc0
    cpnf
    iccssxr
    #
    syl6ss
    wph
    @18
    cxr
    cB
    @24
    esumsup.1
    sseldi
    vz
    @4
    cB
    supxrleub
    syl2anc
    mpbird
    eqbrtrd
end
