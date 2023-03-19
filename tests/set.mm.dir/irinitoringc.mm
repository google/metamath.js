include "zring.mm"
include "cinito.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "chom.mm"
include "co.mm"
include "weu.mm"
include "cbs.mm"
include "wral.mm"
include "wa.mm"
include "csn.mm"
include "wceq.mm"
include "wex.mm"
include "cz.mm"
include "cur.mm"
include "cmg.mm"
include "cmpt.mm"
include "cvv.mm"
include "zex.mm"
include "mptex.mm"
include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "eqid.mm"
include "ringchomfval.mm"
include "adantr.mm"
include "oveqd.mm"
include "crg.mm"
include "cin.mm"
include "id.mm"
include "zringring.mm"
include "a1i.mm"
include "elind.mm"
include "syl.mm"
include "ringcbas.mm"
include "eleqtrrd.mm"
include "simpr.mm"
include "ovresd.mm"
include "eleq2d.mm"
include "elin.mm"
include "simprbi.mm"
include "syl6bi.mm"
include "imp.mm"
include "mulgrhm2.mm"
include "3eqtrd.mm"
include "sneq.mm"
include "eqeq2d.mm"
include "spcegv.mm"
include "mpsyl.mm"
include "eusn.mm"
include "sylibr.mm"
include "ralrimiva.mm"
include "ccat.mm"
include "ringccat.mm"
include "isinito.mm"
include "mpbird.mm"

theorem irinitoringc
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cV: class V
  let vf: setvar f
  let vr: setvar r
  let vz: setvar z
  let vk: setvar k
  let vx: setvar x
  assume irinitoringc.u: |- ( ph -> U e. V )
  assume irinitoringc.z: |- ( ph -> ZZring e. U )
  assume irinitoringc.c: |- C = ( RingCat ` U )


  assert |- ( ph -> ZZring e. ( InitO ` C ) )

  proof
    wph
    zring
    cC
    cinito
    cfv
    wcel
    vf
    cv
    #
    zring
    vr
    cv
    #
    cC
    chom
    cfv
    #
    co
    #
    wcel
    vf
    weu
    #
    vr
    cC
    cbs
    cfv
    #
    wral
    wph
    @4
    vr
    @5
    wph
    @1
    @5
    wcel
    #
    wa
    #
    @3
    @0
    csn
    #
    wceq
    #
    vf
    wex
    #
    @4
    vz
    cz
    vz
    cv
    @1
    cur
    cfv
    #
    @1
    cmg
    cfv
    #
    co
    #
    cmpt
    #
    cvv
    wcel
    @7
    @3
    @14
    csn
    #
    wceq
    #
    @10
    vz
    cz
    @13
    zex
    mptex
    @7
    @3
    zring
    @1
    crh
    @5
    @5
    cxp
    cres
    #
    co
    zring
    @1
    crh
    co
    #
    @15
    @7
    @2
    @17
    zring
    @1
    wph
    @2
    @17
    wceq
    @6
    wph
    @5
    cC
    cU
    @2
    cV
    irinitoringc.c
    @5
    eqid
    #
    irinitoringc.u
    @2
    eqid
    #
    ringchomfval
    adantr
    oveqd
    @7
    zring
    @1
    crh
    @5
    wph
    zring
    @5
    wcel
    @6
    wph
    zring
    cU
    crg
    cin
    #
    @5
    wph
    zring
    cU
    wcel
    #
    zring
    @21
    wcel
    irinitoringc.z
    @22
    cU
    crg
    zring
    @22
    id
    zring
    crg
    wcel
    #
    @22
    zringring
    a1i
    elind
    syl
    wph
    @5
    cC
    cU
    cV
    irinitoringc.c
    @19
    irinitoringc.u
    ringcbas
    #
    eleqtrrd
    adantr
    wph
    @6
    simpr
    ovresd
    @7
    @1
    crg
    wcel
    #
    @18
    @15
    wceq
    wph
    @6
    @25
    wph
    @6
    @1
    @21
    wcel
    #
    @25
    wph
    @5
    @21
    @1
    @24
    eleq2d
    @26
    @1
    cU
    wcel
    @25
    @1
    cU
    crg
    elin
    simprbi
    syl6bi
    imp
    @1
    @12
    @11
    vz
    @14
    @12
    eqid
    @14
    eqid
    @11
    eqid
    mulgrhm2
    syl
    3eqtrd
    @9
    @16
    vf
    @14
    cvv
    @0
    @14
    wceq
    @8
    @15
    @3
    @0
    @14
    sneq
    eqeq2d
    spcegv
    mpsyl
    vf
    @3
    eusn
    sylibr
    ralrimiva
    wph
    @5
    cC
    vf
    @2
    zring
    vr
    @19
    @20
    wph
    cU
    cV
    wcel
    cC
    ccat
    wcel
    irinitoringc.u
    cC
    cU
    cV
    irinitoringc.c
    ringccat
    syl
    wph
    zring
    @21
    @5
    wph
    cU
    crg
    zring
    irinitoringc.z
    @23
    wph
    zringring
    a1i
    elind
    @24
    eleqtrrd
    isinito
    mpbird
end
