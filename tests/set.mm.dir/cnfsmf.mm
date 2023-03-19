include "cdm.mm"
include "nfv.mm"
include "ctop.mm"
include "salgencld.mm"
include "crest.mm"
include "co.mm"
include "cuni.mm"
include "ccn.mm"
include "wcel.mm"
include "wf.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "fdmd.mm"
include "cvv.mm"
include "ovex.mm"
include "uniex.mm"
include "a1i.mm"
include "eqeltrd.mm"
include "unirestss.mm"
include "wss.mm"
include "sssalgen.mm"
include "unissd.mm"
include "sstrd.mm"
include "eqsstrd.mm"
include "cr.mm"
include "wceq.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "feq3d.mm"
include "mpbird.mm"
include "ffdmd.mm"
include "cv.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "csalg.mm"
include "ssrest.mm"
include "syl2anc.mm"
include "adantr.mm"
include "rabeqd.mm"
include "nfcv.mm"
include "cxr.mm"
include "rexr.mm"
include "adantl.mm"
include "rfcnpre2.mm"
include "sseldd.mm"
include "issmfd.mm"

theorem cnfsmf
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vx: setvar x
  let vk: setvar k
  assume cnfsmf.1: |- ( ph -> J e. Top )
  assume cnfsmf.k: |- K = ( topGen ` ran (,) )
  assume cnfsmf.f: |- ( ph -> F e. ( ( J |`t dom F ) Cn K ) )
  assume cnfsmf.s: |- S = ( SalGen ` J )


  assert |- ( ph -> F e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cF
    cdm
    #
    cS
    cF
    va
    wph
    va
    nfv
    wph
    cS
    ctop
    cJ
    cnfsmf.1
    cnfsmf.s
    salgencld
    #
    wph
    @0
    cJ
    @0
    crest
    co
    #
    cuni
    #
    cS
    cuni
    #
    wph
    @3
    cK
    cuni
    #
    cF
    wph
    cF
    @2
    cK
    ccn
    co
    wcel
    #
    @3
    @5
    cF
    wf
    #
    cnfsmf.f
    cF
    @2
    cK
    @3
    @5
    @3
    eqid
    #
    @5
    eqid
    cnf
    syl
    #
    fdmd
    #
    wph
    @3
    cJ
    cuni
    @4
    wph
    cJ
    @0
    ctop
    cvv
    cnfsmf.1
    wph
    @0
    @3
    cvv
    @10
    @3
    cvv
    wcel
    wph
    @2
    cJ
    @0
    crest
    ovex
    uniex
    a1i
    eqeltrd
    unirestss
    wph
    cJ
    cS
    wph
    cJ
    ctop
    wcel
    cJ
    cS
    wss
    #
    cnfsmf.1
    cS
    ctop
    cJ
    cnfsmf.s
    sssalgen
    syl
    #
    unissd
    sstrd
    eqsstrd
    wph
    @3
    cr
    cF
    wph
    @3
    cr
    cF
    wf
    @7
    @9
    wph
    cr
    @5
    cF
    @3
    cr
    @5
    wceq
    wph
    cr
    cioo
    crn
    ctg
    cfv
    #
    cuni
    @5
    uniretop
    cK
    @13
    cnfsmf.k
    unieqi
    eqtr4i
    a1i
    feq3d
    mpbird
    ffdmd
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    @2
    cS
    @0
    crest
    co
    #
    vx
    cv
    cF
    cfv
    @14
    clt
    wbr
    #
    vx
    @0
    crab
    #
    wph
    @2
    @17
    wss
    #
    @15
    wph
    cS
    csalg
    wcel
    @11
    @20
    @1
    @12
    @0
    cJ
    cS
    csalg
    ssrest
    syl2anc
    adantr
    @16
    @19
    @18
    vx
    @3
    crab
    #
    @2
    wph
    @19
    @21
    wceq
    @15
    wph
    @18
    vx
    @0
    @3
    @10
    rabeqd
    adantr
    @16
    vx
    @21
    @14
    cF
    @2
    cK
    @3
    vx
    @14
    nfcv
    vx
    cF
    nfcv
    @16
    vx
    nfv
    cnfsmf.k
    @8
    @21
    eqid
    @15
    @14
    cxr
    wcel
    wph
    @14
    rexr
    adantl
    wph
    @6
    @15
    cnfsmf.f
    adantr
    rfcnpre2
    eqeltrd
    sseldd
    issmfd
end
