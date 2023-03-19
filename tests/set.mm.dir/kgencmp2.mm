include "ctop.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "ckgen.mm"
include "cfv.mm"
include "wa.mm"
include "kgencmp.mm"
include "simpr.mm"
include "eqeltrrd.mm"
include "cuni.mm"
include "ctopon.mm"
include "wss.mm"
include "cvv.mm"
include "cmptop.mm"
include "restrcl.mm"
include "simprd.mm"
include "syl.mm"
include "resttop.mm"
include "sylan2.mm"
include "eqid.mm"
include "toptopon.mm"
include "sylib.mm"
include "cin.mm"
include "wceq.mm"
include "kgenuni.mm"
include "adantr.mm"
include "ineq2d.mm"
include "restuni2.mm"
include "kgenftop.mm"
include "syl2an.mm"
include "3eqtr3d.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "kgenss.mm"
include "ssrest.mm"
include "syl2anc.mm"
include "sscmp.mm"
include "syl3anc.mm"
include "impbida.mm"

theorem kgencmp2
  let cJ: class J
  let cK: class K
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x


  assert |- ( J e. Top -> ( ( J |`t K ) e. Comp <-> ( ( kGen ` J ) |`t K ) e. Comp ) )

  proof
    cJ
    ctop
    wcel
    #
    cJ
    cK
    crest
    co
    #
    ccmp
    wcel
    #
    cJ
    ckgen
    cfv
    #
    cK
    crest
    co
    #
    ccmp
    wcel
    #
    @0
    @2
    wa
    @1
    @4
    ccmp
    cJ
    cK
    kgencmp
    @0
    @2
    simpr
    eqeltrrd
    @0
    @5
    wa
    #
    @1
    @4
    cuni
    #
    ctopon
    cfv
    #
    wcel
    @5
    @1
    @4
    wss
    #
    @2
    @6
    @1
    @1
    cuni
    #
    ctopon
    cfv
    #
    @8
    @6
    @1
    ctop
    wcel
    #
    @1
    @11
    wcel
    @5
    @0
    cK
    cvv
    wcel
    #
    @12
    @5
    @4
    ctop
    wcel
    #
    @13
    @4
    cmptop
    @14
    @3
    cvv
    wcel
    @13
    cK
    @3
    restrcl
    simprd
    syl
    #
    cK
    cJ
    cvv
    resttop
    sylan2
    @1
    @10
    @10
    eqid
    toptopon
    sylib
    @6
    @10
    @7
    ctopon
    @6
    cK
    cJ
    cuni
    #
    cin
    #
    cK
    @3
    cuni
    #
    cin
    #
    @10
    @7
    @6
    @16
    @18
    cK
    @0
    @16
    @18
    wceq
    @5
    cJ
    @16
    @16
    eqid
    #
    kgenuni
    adantr
    ineq2d
    @5
    @0
    @13
    @17
    @10
    wceq
    @15
    cK
    cJ
    cvv
    @16
    @20
    restuni2
    sylan2
    @0
    @3
    ctop
    wcel
    #
    @13
    @19
    @7
    wceq
    @5
    cJ
    kgenftop
    #
    @15
    cK
    @3
    cvv
    @18
    @18
    eqid
    restuni2
    syl2an
    3eqtr3d
    fveq2d
    eleqtrd
    @0
    @5
    simpr
    @6
    @21
    cJ
    @3
    wss
    #
    @9
    @0
    @21
    @5
    @22
    adantr
    @0
    @23
    @5
    cJ
    kgenss
    adantr
    cK
    cJ
    @3
    ctop
    ssrest
    syl2anc
    @1
    @4
    @7
    @7
    eqid
    sscmp
    syl3anc
    impbida
end
