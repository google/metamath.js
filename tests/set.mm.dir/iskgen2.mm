include "ckgen.mm"
include "crn.mm"
include "wcel.mm"
include "ctop.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "kgentop.mm"
include "wceq.mm"
include "kgenidm.mm"
include "eqimss.mm"
include "syl.mm"
include "jca.mm"
include "simpr.mm"
include "kgenss.mm"
include "adantr.mm"
include "eqssd.mm"
include "wfn.mm"
include "wf.mm"
include "kgenf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "eqeltrrd.mm"
include "impbii.mm"

theorem iskgen2
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let cK: class K


  assert |- ( J e. ran kGen <-> ( J e. Top /\ ( kGen ` J ) C_ J ) )

  proof
    cJ
    ckgen
    crn
    #
    wcel
    #
    cJ
    ctop
    wcel
    #
    cJ
    ckgen
    cfv
    #
    cJ
    wss
    #
    wa
    #
    @1
    @2
    @4
    cJ
    kgentop
    @1
    @3
    cJ
    wceq
    @4
    cJ
    kgenidm
    @3
    cJ
    eqimss
    syl
    jca
    @5
    @3
    cJ
    @0
    @5
    @3
    cJ
    @2
    @4
    simpr
    @2
    cJ
    @3
    wss
    @4
    cJ
    kgenss
    adantr
    eqssd
    @2
    @3
    @0
    wcel
    #
    @4
    ckgen
    ctop
    wfn
    #
    @2
    @6
    ctop
    ctop
    ckgen
    wf
    @7
    kgenf
    ctop
    ctop
    ckgen
    ffn
    ax-mp
    ctop
    cJ
    ckgen
    fnfvelrn
    mpan
    adantr
    eqeltrrd
    impbii
end
