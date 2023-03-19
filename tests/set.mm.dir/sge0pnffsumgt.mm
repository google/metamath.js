include "cv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "csu.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cicc.mm"
include "icossicc.mm"
include "sseldi.mm"
include "sge0pnffigtmpt.mm"
include "simpr.mm"
include "wceq.mm"
include "nfv.mm"
include "nfan.mm"
include "elinel2.mm"
include "adantl.mm"
include "simpll.mm"
include "elpwinss.mm"
include "sselda.mm"
include "adantll.mm"
include "syl2anc.mm"
include "sge0fsummptf.mm"
include "adantr.mm"
include "breqtrd.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem sge0pnffsumgt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let cY: class Y
  assume sge0pnffsumgt.k: |- F/ k ph
  assume sge0pnffsumgt.a: |- ( ph -> A e. V )
  assume sge0pnffsumgt.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,) +oo ) )
  assume sge0pnffsumgt.p: |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) = +oo )
  assume sge0pnffsumgt.y: |- ( ph -> Y e. RR )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint Y x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. x e. ( ~P A i^i Fin ) Y < sum_ k e. x B )

  proof
    wph
    cY
    vk
    vx
    cv
    #
    cB
    cmpt
    csumge0
    cfv
    #
    clt
    wbr
    #
    vx
    cA
    cpw
    #
    cfn
    cin
    #
    wrex
    cY
    @0
    cB
    vk
    csu
    #
    clt
    wbr
    #
    vx
    @4
    wrex
    wph
    vx
    cA
    cB
    vk
    cV
    cY
    sge0pnffsumgt.k
    sge0pnffsumgt.a
    wph
    vk
    cv
    #
    cA
    wcel
    #
    wa
    cc0
    cpnf
    cico
    co
    #
    cc0
    cpnf
    cicc
    co
    cB
    cc0
    cpnf
    icossicc
    sge0pnffsumgt.b
    sseldi
    sge0pnffsumgt.p
    sge0pnffsumgt.y
    sge0pnffigtmpt
    wph
    @2
    @6
    vx
    @4
    wph
    @0
    @4
    wcel
    #
    wa
    #
    @2
    @6
    @11
    @2
    wa
    cY
    @1
    @5
    clt
    @11
    @2
    simpr
    @11
    @1
    @5
    wceq
    @2
    @11
    @0
    cB
    vk
    wph
    @10
    vk
    sge0pnffsumgt.k
    @10
    vk
    nfv
    nfan
    @10
    @0
    cfn
    wcel
    wph
    @0
    @3
    cfn
    elinel2
    adantl
    @11
    @7
    @0
    wcel
    #
    wa
    wph
    @8
    cB
    @9
    wcel
    wph
    @10
    @12
    simpll
    @10
    @12
    @8
    wph
    @10
    @0
    cA
    @7
    @0
    cA
    cfn
    elpwinss
    sselda
    adantll
    sge0pnffsumgt.b
    syl2anc
    sge0fsummptf
    adantr
    breqtrd
    ex
    reximdva
    mpd
end
