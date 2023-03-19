include "cesum.mm"
include "csn.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "wcel.mm"
include "wral.mm"
include "cv.mm"
include "ex.mm"
include "ralrimi.mm"
include "esumcl.mm"
include "syl2anc.mm"
include "snidg.mm"
include "syl.mm"
include "eqid.mm"
include "nfcv.mm"
include "fmptdF.mm"
include "cres.mm"
include "cgsu.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "inss1.mm"
include "simpr.mm"
include "sseldi.mm"
include "elpwid.mm"
include "resmptf.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "esumval.mm"
include "xrge0tsmsd.mm"
include "eleqtrrd.mm"

theorem esumel
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume esumel.1: |- F/ k ph
  assume esumel.2: |- F/_ k A
  assume esumel.3: |- ( ph -> A e. V )
  assume esumel.4: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )

  disjoint V k
  disjoint k x
  disjoint A x
  disjoint ph x
  disjoint B x
  assert |- ( ph -> sum* k e. A B e. ( ( RR*s |`s ( 0 [,] +oo ) ) tsums ( k e. A |-> B ) ) )

  proof
    wph
    cA
    cB
    vk
    cesum
    #
    @0
    csn
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    ctsu
    co
    wph
    @0
    @2
    wcel
    #
    @0
    @1
    wcel
    wph
    cA
    cV
    wcel
    cB
    @2
    wcel
    #
    vk
    cA
    wral
    @5
    esumel.3
    wph
    @6
    vk
    cA
    esumel.1
    wph
    vk
    cv
    cA
    wcel
    @6
    esumel.4
    ex
    ralrimi
    cA
    cB
    vk
    cV
    esumel.2
    esumcl
    syl2anc
    @0
    @2
    snidg
    syl
    wph
    cA
    @0
    @4
    @3
    cV
    vx
    @3
    eqid
    esumel.3
    wph
    vk
    cA
    cB
    @2
    @4
    esumel.1
    esumel.2
    vk
    @2
    nfcv
    esumel.4
    @4
    eqid
    fmptdF
    wph
    vx
    cA
    cB
    @3
    @4
    vx
    cv
    #
    cres
    #
    cgsu
    co
    vk
    cV
    esumel.1
    esumel.2
    esumel.3
    esumel.4
    wph
    @7
    cA
    cpw
    #
    cfn
    cin
    #
    wcel
    #
    wa
    #
    vk
    @7
    cB
    cmpt
    #
    @8
    @3
    cgsu
    @12
    @8
    @13
    @12
    @7
    cA
    wss
    @8
    @13
    wceq
    @12
    @7
    cA
    @12
    @10
    @9
    @7
    @9
    cfn
    inss1
    wph
    @11
    simpr
    sseldi
    elpwid
    vk
    cA
    @7
    cB
    esumel.2
    vk
    @7
    nfcv
    resmptf
    syl
    eqcomd
    oveq2d
    esumval
    xrge0tsmsd
    eleqtrrd
end
