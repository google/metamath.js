include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0reval.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "cbvsum.mm"
include "a1i.mm"
include "wral.mm"
include "nfv.mm"
include "nfan.mm"
include "wss.mm"
include "elpwinss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "adantll.mm"
include "simpll.mm"
include "syl2anc.mm"
include "fvmpt2.mm"
include "ex.mm"
include "ralrimi.mm"
include "sumeq2.mm"
include "syl.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "supeq1d.mm"

theorem sge0revalmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let vz: setvar z
  let vk: setvar k
  assume sge0revalmpt.1: |- F/ x ph
  assume sge0revalmpt.2: |- ( ph -> A e. V )
  assume sge0revalmpt.3: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,) +oo ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint ph y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) = sup ( ran ( y e. ( ~P A i^i Fin ) |-> sum_ x e. y B ) , RR* , < ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    csumge0
    cfv
    vy
    cA
    cpw
    cfn
    cin
    #
    vy
    cv
    #
    vz
    cv
    #
    @0
    cfv
    #
    vz
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    vy
    @1
    @2
    cB
    vx
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    wph
    vy
    vz
    @0
    cV
    cA
    sge0revalmpt.2
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cico
    co
    #
    @0
    sge0revalmpt.1
    sge0revalmpt.3
    @0
    eqid
    #
    fmptdf
    sge0reval
    wph
    cxr
    @7
    @10
    clt
    wph
    @6
    @9
    wph
    vy
    @1
    @5
    @8
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @5
    @2
    vx
    cv
    #
    @0
    cfv
    #
    vx
    csu
    #
    @8
    @5
    @17
    wceq
    @14
    @2
    @4
    @16
    vz
    vx
    @3
    @15
    @0
    fveq2
    vx
    @2
    nfcv
    vz
    @2
    nfcv
    vx
    @3
    @0
    vx
    cA
    cB
    nfmpt1
    vx
    @3
    nfcv
    nffv
    vz
    @16
    nfcv
    cbvsum
    a1i
    @14
    @16
    cB
    wceq
    #
    vx
    @2
    wral
    @17
    @8
    wceq
    @14
    @18
    vx
    @2
    wph
    @13
    vx
    sge0revalmpt.1
    @13
    vx
    nfv
    nfan
    @14
    @15
    @2
    wcel
    #
    @18
    @14
    @19
    wa
    #
    @15
    cA
    wcel
    #
    cB
    @11
    wcel
    #
    @18
    @13
    @19
    @21
    wph
    @13
    @19
    wa
    @2
    cA
    @15
    @13
    @2
    cA
    wss
    @19
    @2
    cA
    cfn
    elpwinss
    adantr
    @13
    @19
    simpr
    sseldd
    adantll
    #
    @20
    wph
    @21
    @22
    wph
    @13
    @19
    simpll
    @23
    sge0revalmpt.3
    syl2anc
    vx
    cA
    cB
    @11
    @0
    @12
    fvmpt2
    syl2anc
    ex
    ralrimi
    @2
    @16
    cB
    vx
    sumeq2
    syl
    eqtrd
    mpteq2dva
    rneqd
    supeq1d
    eqtrd
end
