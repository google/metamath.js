include "cfv.mm"
include "cc0.mm"
include "cdgr.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "ccoe.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cply.mm"
include "wcel.mm"
include "cc.mm"
include "wceq.mm"
include "wss.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cnfldbas.mm"
include "subrgss.mm"
include "syl.mm"
include "plyss.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "eqid.mm"
include "coeid2.mm"
include "fzfid.mm"
include "wa.mm"
include "adantr.mm"
include "cn0.mm"
include "wf.mm"
include "csubg.mm"
include "subrgsubg.mm"
include "cnfld0.mm"
include "subg0cl.mm"
include "3syl.mm"
include "coef2.mm"
include "elfznn0.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "cnsrexpcl.mm"
include "cnfldmul.mm"
include "subrgmcl.mm"
include "syl3anc.mm"
include "fsumcnsrcl.mm"
include "eqeltrd.mm"

theorem cnsrplycl
  let wph: wff ph
  let cC: class C
  let cP: class P
  let cS: class S
  let cX: class X
  let vk: setvar k
  assume cnsrplycl.s: |- ( ph -> S e. ( SubRing ` CCfld ) )
  assume cnsrplycl.p: |- ( ph -> P e. ( Poly ` C ) )
  assume cnsrplycl.x: |- ( ph -> X e. S )
  assume cnsrplycl.c: |- ( ph -> C C_ S )


  assert |- ( ph -> ( P ` X ) e. S )

  proof
    wph
    cX
    cP
    cfv
    #
    cc0
    cP
    cdgr
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cP
    ccoe
    cfv
    #
    cfv
    #
    cX
    @3
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cS
    wph
    cP
    cS
    cply
    cfv
    #
    wcel
    #
    cX
    cc
    wcel
    @0
    @8
    wceq
    wph
    cC
    cply
    cfv
    #
    @9
    cP
    wph
    cC
    cS
    wss
    cS
    cc
    wss
    #
    @11
    @9
    wss
    cnsrplycl.c
    wph
    cS
    ccnfld
    csubrg
    cfv
    wcel
    #
    @12
    cnsrplycl.s
    cS
    cc
    ccnfld
    cnfldbas
    subrgss
    syl
    #
    cC
    cS
    plyss
    syl2anc
    cnsrplycl.p
    sseldd
    #
    wph
    cS
    cc
    cX
    @14
    cnsrplycl.x
    sseldd
    @4
    cS
    vk
    cP
    @1
    cX
    @4
    eqid
    #
    @1
    eqid
    coeid2
    syl2anc
    wph
    @2
    @7
    cS
    vk
    cnsrplycl.s
    wph
    cc0
    @1
    fzfid
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @13
    @5
    cS
    wcel
    @6
    cS
    wcel
    @7
    cS
    wcel
    wph
    @13
    @17
    cnsrplycl.s
    adantr
    #
    @18
    cn0
    cS
    @3
    @4
    wph
    cn0
    cS
    @4
    wf
    #
    @17
    wph
    @10
    cc0
    cS
    wcel
    #
    @20
    @15
    wph
    @13
    cS
    ccnfld
    csubg
    cfv
    wcel
    @21
    cnsrplycl.s
    cS
    ccnfld
    subrgsubg
    cS
    ccnfld
    cc0
    cnfld0
    subg0cl
    3syl
    @4
    cS
    cP
    @16
    coef2
    syl2anc
    adantr
    @17
    @3
    cn0
    wcel
    wph
    @3
    @1
    elfznn0
    adantl
    #
    ffvelrnd
    @18
    cS
    cX
    @3
    @19
    wph
    cX
    cS
    wcel
    @17
    cnsrplycl.x
    adantr
    @22
    cnsrexpcl
    cS
    ccnfld
    cmul
    @5
    @6
    cnfldmul
    subrgmcl
    syl3anc
    fsumcnsrcl
    eqeltrd
end
