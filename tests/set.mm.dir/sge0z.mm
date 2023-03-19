include "cc0.mm"
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
include "csn.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "0e0icopnf.mm"
include "a1i.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0reval.mm"
include "wceq.mm"
include "cc.mm"
include "eqidd.mm"
include "wss.mm"
include "elpwinss.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "0cnd.mm"
include "fvmptd.mm"
include "adantll.mm"
include "sumeq2dv.mm"
include "cuz.mm"
include "wo.mm"
include "elinel2.mm"
include "olc.mm"
include "syl.mm"
include "sumz.mm"
include "adantl.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "c0.mm"
include "wne.mm"
include "pwfin0.mm"
include "rnmptc.mm"
include "supeq1d.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "supsn.mm"
include "syl2anc.mm"
include "3eqtrd.mm"

theorem sge0z
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  assume sge0z.1: |- F/ k ph
  assume sge0z.2: |- ( ph -> A e. V )

  disjoint A k
  disjoint A x
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> 0 ) ) = 0 )

  proof
    wph
    vk
    cA
    cc0
    cmpt
    #
    csumge0
    cfv
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    cfv
    #
    vy
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    wph
    vx
    vy
    @0
    cV
    cA
    sge0z.2
    wph
    vk
    cA
    cc0
    cc0
    cpnf
    cico
    co
    #
    @0
    sge0z.1
    cc0
    @11
    wcel
    wph
    vk
    cv
    #
    cA
    wcel
    wa
    0e0icopnf
    a1i
    @0
    eqid
    fmptdf
    sge0reval
    wph
    cxr
    @8
    @9
    clt
    wph
    @8
    vx
    @2
    cc0
    cmpt
    #
    crn
    @9
    wph
    @7
    @13
    wph
    vx
    @2
    @6
    cc0
    wph
    @3
    @2
    wcel
    #
    wa
    #
    @6
    @3
    cc0
    vy
    csu
    #
    cc0
    @15
    @3
    @5
    cc0
    vy
    @14
    @4
    @3
    wcel
    #
    @5
    cc0
    wceq
    wph
    @14
    @17
    wa
    #
    vk
    @4
    cc0
    cc0
    cA
    @0
    cc
    @18
    @0
    eqidd
    cc0
    cc0
    wceq
    @18
    @12
    @4
    wceq
    wa
    cc0
    eqid
    a1i
    @18
    @3
    cA
    @4
    @14
    @3
    cA
    wss
    @17
    @3
    cA
    cfn
    elpwinss
    adantr
    @14
    @17
    simpr
    sseldd
    @18
    0cnd
    fvmptd
    adantll
    sumeq2dv
    @14
    @16
    cc0
    wceq
    #
    wph
    @14
    @3
    cB
    cuz
    cfv
    wss
    #
    @3
    cfn
    wcel
    #
    wo
    #
    @19
    @14
    @21
    @22
    @3
    @1
    cfn
    elinel2
    @21
    @20
    olc
    syl
    @3
    vy
    cB
    sumz
    syl
    adantl
    eqtrd
    mpteq2dva
    rneqd
    wph
    vx
    @2
    cc0
    cc
    @13
    @13
    eqid
    @15
    0cnd
    @2
    c0
    wne
    wph
    cA
    pwfin0
    a1i
    rnmptc
    eqtrd
    supeq1d
    wph
    cxr
    clt
    wor
    #
    cc0
    cxr
    wcel
    #
    @10
    cc0
    wceq
    @23
    wph
    xrltso
    a1i
    @24
    wph
    0xr
    a1i
    cxr
    cc0
    clt
    supsn
    syl2anc
    3eqtrd
end
