include "cflim.mm"
include "co.mm"
include "wcel.mm"
include "cuni.mm"
include "cfil.mm"
include "cfv.mm"
include "crn.mm"
include "ctop.mm"
include "cpw.mm"
include "wss.mm"
include "w3a.mm"
include "csn.mm"
include "cnei.mm"
include "wa.mm"
include "elflim2.mm"
include "simplbi.mm"
include "simp2d.mm"
include "filunirn.mm"
include "sylib.mm"
include "simp3d.mm"
include "sspwuni.mm"
include "flimneiss.mm"
include "flimtop.mm"
include "topopn.mm"
include "syl.mm"
include "flimelbas.mm"
include "opnneip.mm"
include "syl3anc.mm"
include "sseldd.mm"
include "elssuni.mm"
include "eqssd.mm"
include "fveq2d.mm"
include "eleqtrd.mm"

theorem flimfil
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  assume flimuni.1: |- X = U. J


  assert |- ( A e. ( J fLim F ) -> F e. ( Fil ` X ) )

  proof
    cA
    cJ
    cF
    cflim
    co
    wcel
    #
    cF
    cF
    cuni
    #
    cfil
    cfv
    #
    cX
    cfil
    cfv
    @0
    cF
    cfil
    crn
    cuni
    wcel
    #
    cF
    @2
    wcel
    @0
    cJ
    ctop
    wcel
    #
    @3
    cF
    cX
    cpw
    wss
    #
    @0
    @4
    @3
    @5
    w3a
    cA
    cX
    wcel
    #
    cA
    csn
    cJ
    cnei
    cfv
    cfv
    #
    cF
    wss
    wa
    cA
    cF
    cJ
    cX
    flimuni.1
    elflim2
    simplbi
    #
    simp2d
    cF
    filunirn
    sylib
    @0
    @1
    cX
    cfil
    @0
    @1
    cX
    @0
    @5
    @1
    cX
    wss
    @0
    @4
    @3
    @5
    @8
    simp3d
    cF
    cX
    sspwuni
    sylib
    @0
    cX
    cF
    wcel
    cX
    @1
    wss
    @0
    @7
    cF
    cX
    cA
    cF
    cJ
    flimneiss
    @0
    @4
    cX
    cJ
    wcel
    #
    @6
    cX
    @7
    wcel
    cA
    cF
    cJ
    flimtop
    #
    @0
    @4
    @9
    @10
    cJ
    cX
    flimuni.1
    topopn
    syl
    cA
    cF
    cJ
    cX
    flimuni.1
    flimelbas
    cA
    cJ
    cX
    opnneip
    syl3anc
    sseldd
    cX
    cF
    elssuni
    syl
    eqssd
    fveq2d
    eleqtrd
end
