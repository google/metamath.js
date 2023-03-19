include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wa.mm"
include "cflim.mm"
include "co.mm"
include "cuni.mm"
include "csn.mm"
include "cnei.mm"
include "wss.mm"
include "ctop.mm"
include "crn.mm"
include "cpw.mm"
include "wb.mm"
include "topontop.mm"
include "adantr.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "adantl.mm"
include "filsspw.mm"
include "wceq.mm"
include "toponuni.mm"
include "pweqd.mm"
include "sseqtrd.mm"
include "w3a.mm"
include "eqid.mm"
include "elflim2.mm"
include "baib.mm"
include "syl3anc.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "bitr4d.mm"

theorem elflim
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X


  assert |- ( ( J e. ( TopOn ` X ) /\ F e. ( Fil ` X ) ) -> ( A e. ( J fLim F ) <-> ( A e. X /\ ( ( nei ` J ) ` { A } ) C_ F ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cX
    cfil
    cfv
    #
    wcel
    #
    wa
    #
    cA
    cJ
    cF
    cflim
    co
    wcel
    #
    cA
    cJ
    cuni
    #
    wcel
    #
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    cF
    wss
    #
    wa
    #
    cA
    cX
    wcel
    #
    @7
    wa
    @3
    cJ
    ctop
    wcel
    #
    cF
    cfil
    crn
    cuni
    #
    wcel
    #
    cF
    @5
    cpw
    #
    wss
    #
    @4
    @8
    wb
    @0
    @10
    @2
    cX
    cJ
    topontop
    adantr
    @2
    @12
    @0
    @1
    @11
    cF
    cfil
    cX
    fvssunirn
    sseli
    adantl
    @3
    cF
    cX
    cpw
    #
    @13
    @2
    cF
    @15
    wss
    @0
    cF
    cX
    filsspw
    adantl
    @3
    cX
    @5
    @0
    cX
    @5
    wceq
    @2
    cX
    cJ
    toponuni
    adantr
    #
    pweqd
    sseqtrd
    @4
    @10
    @12
    @14
    w3a
    @8
    cA
    cF
    cJ
    @5
    @5
    eqid
    elflim2
    baib
    syl3anc
    @3
    @9
    @6
    @7
    @3
    cX
    @5
    cA
    @16
    eleq2d
    anbi1d
    bitr4d
end
