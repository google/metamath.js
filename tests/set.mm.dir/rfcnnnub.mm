include "cv.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cn.mm"
include "wrex.mm"
include "wex.mm"
include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "w3a.mm"
include "wa.mm"
include "nfcv.mm"
include "nfv.mm"
include "ccn.mm"
include "co.mm"
include "syl6eleq.mm"
include "evthf.mm"
include "df-rex.mm"
include "sylib.mm"
include "fcnre.mm"
include "ffvelrnda.mm"
include "ex.mm"
include "anim1d.mm"
include "eximdv.mm"
include "mpd.mm"
include "ralrimi.mm"
include "19.41v.mm"
include "sylanbrc.mm"
include "df-3an.mm"
include "exbii.mm"
include "sylibr.mm"
include "nffv.mm"
include "nfel1.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfbr.mm"
include "nfan.mm"
include "simpll3.mm"
include "simpr.mm"
include "rsp.mm"
include "sylc.mm"
include "simpll1.mm"
include "simplrl.mm"
include "nnred.mm"
include "simpl2.mm"
include "r19.21bi.mm"
include "simplrr.mm"
include "lelttrd.mm"
include "arch.mm"
include "3ad2ant1.mm"
include "reximddv.mm"
include "eximi.mm"
include "syl.mm"
include "19.9v.mm"

theorem rfcnnnub
  let wph: wff ph
  let vt: setvar t
  let cC: class C
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cK: class K
  let vs: setvar s
  assume rfcnnnub.1: |- F/_ t F
  assume rfcnnnub.2: |- F/ t ph
  assume rfcnnnub.3: |- K = ( topGen ` ran (,) )
  assume rfcnnnub.4: |- ( ph -> J e. Comp )
  assume rfcnnnub.5: |- T = U. J
  assume rfcnnnub.6: |- ( ph -> T =/= (/) )
  assume rfcnnnub.7: |- C = ( J Cn K )
  assume rfcnnnub.8: |- ( ph -> F e. C )

  disjoint n t
  disjoint T n
  disjoint T t
  disjoint F n
  disjoint J t
  disjoint K t
  disjoint n s
  disjoint s t
  disjoint T s
  disjoint F s
  disjoint J s
  disjoint ph s
  assert |- ( ph -> E. n e. NN A. t e. T ( F ` t ) < n )

  proof
    wph
    vt
    cv
    #
    cF
    cfv
    #
    vn
    cv
    #
    clt
    wbr
    #
    vt
    cT
    wral
    #
    vn
    cn
    wrex
    #
    vs
    wex
    #
    @5
    wph
    vs
    cv
    #
    cF
    cfv
    #
    cr
    wcel
    #
    @1
    @8
    cle
    wbr
    #
    vt
    cT
    wral
    #
    @1
    cr
    wcel
    #
    vt
    cT
    wral
    #
    w3a
    #
    vs
    wex
    #
    @6
    wph
    @9
    @11
    wa
    #
    @13
    wa
    #
    vs
    wex
    #
    @15
    wph
    @16
    vs
    wex
    #
    @13
    @18
    wph
    @7
    cT
    wcel
    #
    @11
    wa
    #
    vs
    wex
    #
    @19
    wph
    @11
    vs
    cT
    wrex
    @22
    wph
    vs
    vt
    cF
    cJ
    cK
    cT
    vs
    cF
    nfcv
    rfcnnnub.1
    vs
    cT
    nfcv
    vt
    cT
    nfcv
    wph
    vs
    nfv
    rfcnnnub.2
    rfcnnnub.5
    rfcnnnub.3
    rfcnnnub.4
    wph
    cF
    cC
    cJ
    cK
    ccn
    co
    rfcnnnub.8
    rfcnnnub.7
    syl6eleq
    rfcnnnub.6
    evthf
    @11
    vs
    cT
    df-rex
    sylib
    wph
    @21
    @16
    vs
    wph
    @20
    @9
    @11
    wph
    @20
    @9
    wph
    cT
    cr
    @7
    cF
    wph
    cC
    cT
    cF
    cJ
    cK
    rfcnnnub.3
    rfcnnnub.5
    rfcnnnub.7
    rfcnnnub.8
    fcnre
    #
    ffvelrnda
    ex
    anim1d
    eximdv
    mpd
    wph
    @12
    vt
    cT
    rfcnnnub.2
    wph
    @0
    cT
    wcel
    #
    @12
    wph
    cT
    cr
    @0
    cF
    @23
    ffvelrnda
    ex
    ralrimi
    @16
    @13
    vs
    19.41v
    sylanbrc
    @14
    @17
    vs
    @9
    @11
    @13
    df-3an
    exbii
    sylibr
    @14
    @5
    vs
    @14
    @8
    @2
    clt
    wbr
    #
    @4
    vn
    cn
    @14
    @2
    cn
    wcel
    #
    @25
    wa
    #
    wa
    #
    @3
    vt
    cT
    @14
    @27
    vt
    @9
    @11
    @13
    vt
    vt
    @8
    cr
    vt
    @7
    cF
    rfcnnnub.1
    vt
    @7
    nfcv
    nffv
    #
    nfel1
    @10
    vt
    cT
    nfra1
    @12
    vt
    cT
    nfra1
    nf3an
    @26
    @25
    vt
    @26
    vt
    nfv
    vt
    @8
    @2
    clt
    @29
    vt
    clt
    nfcv
    vt
    @2
    nfcv
    nfbr
    nfan
    nfan
    @28
    @24
    @3
    @28
    @24
    wa
    #
    @1
    @8
    @2
    @30
    @13
    @24
    @12
    @9
    @11
    @13
    @27
    @24
    simpll3
    @28
    @24
    simpr
    @12
    vt
    cT
    rsp
    sylc
    @9
    @11
    @13
    @27
    @24
    simpll1
    @30
    @2
    @14
    @26
    @25
    @24
    simplrl
    nnred
    @28
    @10
    vt
    cT
    @9
    @11
    @13
    @27
    simpl2
    r19.21bi
    @14
    @26
    @25
    @24
    simplrr
    lelttrd
    ex
    ralrimi
    @9
    @11
    @25
    vn
    cn
    wrex
    @13
    @8
    vn
    arch
    3ad2ant1
    reximddv
    eximi
    syl
    @5
    vs
    19.9v
    sylib
end
